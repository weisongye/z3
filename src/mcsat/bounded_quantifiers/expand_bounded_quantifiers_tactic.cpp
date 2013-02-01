/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    bounded_quantifiers_tactic.cpp

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-01-17.

--*/
#include"tactical.h"
#include"rewriter_def.h"
#include"var_subst.h"
#include"bound_info.h"
#include"ast_pp.h"
#include"ast_util.h"
#include"th_rewriter.h"
#include"normalize_bounded_quantifiers_tactic.h"
#include"expand_bounded_quantifiers_params.hpp"
#include"assertion_stream.h"
#include"has_free_vars.h"

class numeral_bound_recognizer
{
private:
    ast_manager & m_m;
    arith_util & m_au;
    bv_util & m_bvu;
    th_rewriter & m_as;
    bool get_constant(sort * s, expr * bnd, rational & range) {
        if (m_au.is_int(s)) {
            if (m_au.is_numeral(bnd, range)) {
                return true;
            }
        }
        else if (m_bvu.is_bv_sort(s)) {
            unsigned sz;
            if (m_bvu.is_numeral(bnd, range, sz)) {
                return true;
            }
        }
        return false;
    }
    //determine if ite_term encodes the minimum or maximum function
    bool is_min_max_func(expr* ite_term, bool isMax) {
        if (m_m.is_ite(ite_term)) {
            if (m_au.is_le(to_app(ite_term)->get_arg(0)) || m_bvu.is_bv_ule(to_app(ite_term)->get_arg(0))) {
                bool isReverse = isMax;
                for (unsigned i = 0; i <= 1; i++) {
                    unsigned io = isReverse ? (i==1 ? 1 : 0) : i;
                    if (to_app(ite_term)->get_arg(i+1)!=to_app(to_app(ite_term)->get_arg(0))->get_arg(io)) {
                        return false;
                    }
                }
                return true;
            }
        }
        return false;
    }
public:
    //currently all ite conditions must be "less than or equal"
    numeral_bound_recognizer(ast_manager & m, arith_util & au, bv_util & bvu, th_rewriter & as) : 
      m_m(m), m_au(au), m_bvu(bvu), m_as(as), m_infer_ite_bounds(true) {}
    bool m_infer_ite_bounds;

    bool get_constant_bound(sort * s, expr * bnd, bool isMax, rational & range) {
        if (m_infer_ite_bounds && is_min_max_func(bnd, isMax)) {
            bool foundBound = false;
            for (unsigned i = 1; i <= 2; i++) {
                rational r;
                if (get_constant_bound(s, to_app(bnd)->get_arg(i), isMax, r)) {
                    if (!foundBound || (isMax ? r>range : r<range)) {
                        range = r;
                    }
                    foundBound = true;
                }
            }
            return foundBound;
        }
        else if (m_au.is_add(bnd) || m_au.is_mul(bnd)) {
            //recurse on children
            expr_ref_buffer child_t(m_m);
            for (unsigned i=0; i<to_app(bnd)->get_num_args(); i++) {
                rational r;
                if (get_constant_bound(s, to_app(bnd)->get_arg(i), isMax, r)) {
                    child_t.push_back(m_au.mk_numeral(r, true));
                }
                else {
                    //could not find constant bound, return false
                    return false;
                }
            }
            expr_ref child(m_m);
            child = m_au.is_add(bnd) ? m_au.mk_add(child_t.size(), child_t.c_ptr()) : m_au.mk_mul(child_t.size(), child_t.c_ptr());
            //simplify the child
            m_as(child, child);
            if (m_au.is_numeral(child, range)) {
                return true;
            }
            return false;
        }
        else {
            return get_constant(s, bnd, range);
        }
    }
};

class cardinality_bound_recognizer
{
private:
    ast_manager & m_m;
    bool get_cardinality_bound_eq(expr * e, ptr_vector<expr> & reps ) {
        if (m_m.is_eq(e)) {
            app* eq = to_app(e);
            for (unsigned j = 0; j < 2; j++) {
                unsigned jo = j == 0 ? 1 : 0;
                if (is_var(eq->get_arg(j)) && to_var(eq->get_arg(j))->get_idx()==0 && 
                    is_ground(eq->get_arg(jo))) {
                    reps.push_back(eq->get_arg(jo));
                    return true;
                }
            }
        }
        return false;
    }
public:
    //currently all ite conditions must be "less than or equal"
    cardinality_bound_recognizer(ast_manager & m) :  m_m(m) {}
    bool get_cardinality_bound(expr* bnd, sort * & s, ptr_vector<expr> & reps ) {
        if (is_quantifier(bnd)) {
            quantifier * q = to_quantifier(bnd);
            if (q->get_num_decls()==1) {
                s = q->get_decl_sort(0);
                expr* body = q->get_expr();
                if (m_m.is_or(body)) {
                    for (unsigned i = 0; i < to_app(body)->get_num_args(); i++) {
                        if (!get_cardinality_bound_eq(to_app(body)->get_arg(i), reps)) {
                            return false;
                        }
                    }
                    return true;
                }
                else {
                    return get_cardinality_bound_eq(body, reps);
                }
            }
        }
        return false;
    }
    //outputs into result (reps is input)
    static void mk_cardinality_bound(ast_manager & m, sort * s, const symbol & sym, ptr_vector<expr> & reps, expr_ref & result) {
        if (reps.empty()) {
            result = m.mk_false();
        }
        else {
            var_ref v(m);
            v = m.mk_var(0, s);
            expr_ref_buffer eqs(m);
            for (unsigned i = 0; i < reps.size(); i++) {
                eqs.push_back(m.mk_eq(v, reps[i]));
            }
            result = reps.size() > 1 ? m.mk_or(eqs.size(), eqs.c_ptr()) : eqs[0];
            //make the quantifier
            ptr_buffer<sort> sorts;
            sbuffer<symbol> symbols;
            sorts.push_back(s);
            symbols.push_back(sym);
            result = m.mk_forall(sorts.size(), sorts.c_ptr(), symbols.c_ptr(), result);
        }
    }
    //outputs into result_reps, result
    static void mk_cardinality_bound(ast_manager & m, sort * s, const symbol & sym, unsigned bound, ptr_vector<expr> & result_reps, expr_ref & result) {
        for (unsigned i = 0; i < bound; i++) {
            result_reps.push_back(m.mk_fresh_const("c",s));
        }
        mk_cardinality_bound(m, s, sym, result_reps, result);
    }
};

//expand bounded quantifiers tactic
class expand_bounded_quantifiers_tactic : public tactic {

    struct rw_cfg : public default_rewriter_cfg {
    public:
        bool process(bound_info & bi, unsigned index, expr_ref_buffer & val_subs, expr_ref_buffer & exp_result) {
            if (index == bi.m_var_order.size()) {
                if (m_inst_count >= m_opt_max_instances) {
                    return false;
                }
                else {
                    m_inst_count++;
                    //add body substituted for the values in vals
                    expr_ref subs_body(m_m);
                    instantiate(m_m, bi.m_q, val_subs.c_ptr(), subs_body);
                    arith_simp(subs_body,subs_body);
                    exp_result.push_back(subs_body);
                    return true;
                }
            }
            else {
                unsigned i = bi.m_var_order[index];
                sort * s = bi.m_q->get_decl_sort(bi.m_q->get_num_decls()-1-i);
                //calculate the range
                expr_ref upper(m_m);
                //find the constant range
                rational range;
                bool success = false;
                //try to find a constant bound
                if (m_au.is_int(s) || m_bvu.is_bv_sort(s)) {
                    upper = bi.get_upper_bound(i);
                    //apply substitution to "upper" based on val_subs
                    SASSERT(bi.m_q->get_num_decls() == val_subs.size());
                    instantiate(m_m, upper, val_subs.size(), val_subs.c_ptr(), upper);
                    //rewrite upper?
                    arith_simp(upper,upper);
                    TRACE("expand_bounded_quantifiers-debug", tout << "Compute constant bound for " << mk_pp(upper, m_m) << ", infer ite : " << m_opt_use_constant_bounds << "\n";);
                    numeral_bound_recognizer nbr(m_m, m_au, m_bvu, arith_simp);
                    nbr.m_infer_ite_bounds = m_opt_use_constant_bounds;
                    if (nbr.get_constant_bound(s, upper, false, range)) {
                        success = true;
                    }
                }
                else if (m_m.is_uninterp(s)) {
                    //see if there is a constant cardinality bound on s
                    if (m_cardinality_bounds.contains(s)) {
                        success = true;
                        range = rational(m_cardinality_bounds.find(s).size()-1);
                        TRACE("expand_bounded_quantifiers-debug", tout << "Found preexisting cardinality " << m_cardinality_bounds.find(s).size() << "\n";);
                    }
                }
                //add symbolic bound if necessary
                if (!success && !m_opt_precise) {
                    range = rational(m_opt_domain - 1); //minus one since we have a non-strict lower bound of zero
                    //must add constraint to result to make it constant
                    expr_ref bnd(m_m);
                    if (m_au.is_int(s)) {
                        TRACE("expand_bounded_quantifiers-debug", tout << "Add symbolic constraint " << mk_pp(upper, m_m) << " <= " << (m_opt_domain - 1) << "\n";);
                        bnd = m_au.mk_le(upper, m_au.mk_numeral(range, true));
                        success = true;
                    }
                    else if (m_bvu.is_bv_sort(s)) {
                        TRACE("expand_bounded_quantifiers-debug", tout << "Add symbolic constraint " << mk_pp(upper, m_m) << " <= " << (m_opt_domain - 1) << "\n";);
                        bnd = m_bvu.mk_ule(upper, m_bvu.mk_numeral(range, s));
                        success = true;
                    }
                    else if (m_m.is_uninterp(s)) {
                        TRACE("expand_bounded_quantifiers-debug", tout << "Adding symbolic cardinality constraint...\n";);
                        //assert cardinality bound if not already there
                        m_cardinality_bounds.insert(s, ptr_vector<expr>());
                        symbol sym("x");
                        cardinality_bound_recognizer::mk_cardinality_bound(m_m, s, sym, m_opt_domain, m_cardinality_bounds.find(s), bnd);
                        success = true;
                        TRACE("expand_bounded_quantifiers-debug", tout << "Added constraint " << mk_pp(bnd, m_m) << "\n";);
                    }
                    if (success) {
                        //add bound to outermost conjunction if not done so already
                        if (!exp_result.contains(bnd)) {
                            m_precise = false;
                            exp_result.push_back(bnd);
                        }
                    }
                }
                //if we found a valid range
                if (success) {
                    //if the range if non-negative
                    if (range.is_nonneg()) {
                        if (!range.is_uint64() || range.get_uint64() > UINT_MAX)
                            return false;
                        unsigned _range = static_cast<unsigned>(range.get_uint64());
                        //iterate over all values in the range
                        for (unsigned v = 0; v <= _range; v++) {
                            expr_ref val(m_m);
                            if (m_au.is_int(s)) {
                                val = m_au.mk_numeral(rational(v), true);
                            }
                            else if (m_bvu.is_bv_sort(s)) {
                                val = m_bvu.mk_numeral(rational(v),s);
                            }
                            else if (m_m.is_uninterp(s)) {
                                val = m_cardinality_bounds.find(s)[v];
                            }
                            val_subs.setx(bi.m_q->get_num_decls() - 1 - i, val);
                            TRACE("expand_bounded_quantifiers-debug", tout << "Consider " << v << " / " << i << "\n";);
                            //see if the current body is true or false
                            bool considerInst = true;
                            if (m_opt_filter_instances) {
                                expr_ref subs_body(m_m);
                                var_subst vs(m_m);
                                vs(bi.m_q->get_expr(), val_subs.size(), val_subs.c_ptr(), subs_body);
                                arith_simp(subs_body,subs_body);
                                if (m_m.is_true(subs_body)) {
                                    TRACE("expand_bounded_quantifiers-debug", tout << "Current instance does not matter.\n";);
                                    //this instance does not matter
                                    considerInst = false;
                                }
                                else if (m_m.is_false(subs_body)) {
                                    //we have found a false instance, the quantifier can be simplified to false
                                    TRACE("expand_bounded_quantifiers-debug", tout << "Current instance does not matter.\n";);
                                    m_is_falsified = true;
                                    return true;
                                }
                            }
                            if (considerInst) {
                                if (!process(bi, index+1, val_subs, exp_result)) {
                                    return false;
                                }
                            }
                        }
                    }
                    return true;
                }
                else {
                    TRACE("expand_bounded_quantifiers", tout << "Could not process upper bound " << mk_pp(upper, m_m) << "\n";);
                    return false;
                }
            }
        }
        // current # of instances we have added
        unsigned m_inst_count;
        // current # of instances we have tested
        unsigned m_inst_test_count;
        // is the conversion precise?
        bool m_precise;
        // is the quantifier falsified, i.e. did we find a false instance?
        bool m_is_falsified;
    public:
        ast_manager & m_m;
        arith_util m_au;
        bv_util m_bvu;
        th_rewriter arith_simp;
        //options information
        unsigned m_opt_domain;
        unsigned m_opt_max_instances;
        unsigned m_opt_max_test_instances;
        bool m_opt_precise;
        bool m_opt_use_constant_bounds;
        bool m_opt_filter_instances;
        //other information
        bool m_had_nested_quantifiers;
        obj_map< sort, ptr_vector<expr> > m_cardinality_bounds;

        rw_cfg(ast_manager & _m, params_ref const & p):
            m_m(_m), m_au(_m), m_bvu(_m), arith_simp(_m){
            params_ref arith_p;
            arith_p.set_bool("sort_sums", true);
            arith_p.set_bool("ule-split", false);
            arith_simp.updt_params(arith_p);
            m_inst_count = 0;
            m_inst_test_count = 0;
            m_precise = true;
            m_is_falsified = false;
	        updt_params(p);
        }

        void updt_params(params_ref const & _p) {
            expand_bounded_quantifiers_params p(_p);
            m_opt_domain              = p.domain();
            m_opt_max_instances       = p.max_instances();
            m_opt_max_test_instances  = p.max_test_instances();
            m_opt_precise             = p.precise();
            m_opt_use_constant_bounds = p.use_constant_bounds();
            m_opt_filter_instances    = p.filter_instances();
        }
        bool is_precise() { return m_precise; }
        
        bool reduce_quantifier(quantifier * old_q, 
                               expr * new_body, 
                               expr * const * new_patterns, 
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {
            quantifier_ref q(m_m);
            q = m_m.update_quantifier(old_q, old_q->get_num_patterns(), new_patterns, old_q->get_num_no_patterns(), new_no_patterns, new_body);
            if (has_free_vars(q)) {
                TRACE("expand_bounded_quantifiers", tout << mk_pp(q,m_m) << " has free variables.\n";);
                m_had_nested_quantifiers = true;
            }
            else {
                TRACE("expand_bounded_quantifiers", tout << "Process " << mk_pp(q, m_m) << "\n";);
                bound_info bi(m_m, m_au, m_bvu, q);
                if (bi.compute()) {
                    //check that all lower bounds are zero
                    if (bi.is_normalized()) {
                        TRACE("expand_bounded_quantifiers", bi.display(tout););
                        //we will rewrite the quantifier into a conjunction based on expansion
                        //the values we make for each variable
                        expr_ref_buffer val_subs(m_m);
                        for (unsigned i = 0; i < q->get_num_decls(); i++) {
                            sort * s = q->get_decl_sort(i);
                            expr * v = m_m.mk_var(q->get_num_decls()-1-i, s);
                            val_subs.push_back(v);
                        }
                        //simplify the new body of quantifier
                        TRACE("expand_bounded_quantifiers-debug", tout << "Simplify the body...\n";);
                        expr_ref body(m_m);
                        body = q->get_expr();
                        arith_simp(body,body);
                        bi.m_q = m_m.update_quantifier(q,body);
                        //conjunction of formulas in the result
                        expr_ref_buffer exp_result(m_m);
                        //now, populate the result buffer
                        m_inst_count = 0;
                        m_inst_test_count = 0;
                        TRACE("expand_bounded_quantifiers-debug", tout << "Process the expansion...\n";);
                        if (process(bi, 0, val_subs, exp_result)) {
                            //result is a conjunction of the literals in exp_result
                            result = m_is_falsified ? m_m.mk_false() : mk_and(m_m, exp_result.size(), exp_result.c_ptr());
                            TRACE("expand_bounded_quantifiers", tout << "Expand, got result " << mk_pp(result, m_m) << "\n";);
                            return true;
                        }
                        else {
                            TRACE("expand_bounded_quantifiers",tout << "Bound expansion failed (too many instances).\n";);
                        }
                    }
                    else {
                        TRACE("expand_bounded_quantifiers",tout << "Bounds are not normalized.\n";);
                    }
                }
                else {
                    TRACE("expand_bounded_quantifiers",tout << "Could not find bounds.\n";);
                }
            }
            return false;
        }
    };

    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;
        rw(ast_manager & m, params_ref const & p):
            rewriter_tpl<rw_cfg>(m, false, m_cfg),
            m_cfg(m, p) {
        }
        bool is_precise() { return m_cfg.is_precise(); }
    };

    rw            m_rw;
    params_ref    m_params;

    void apply_rewrite(expr * curr, expr_ref & result) {
        //TODO: collect all preexisting cardinality bounds
        do {
            m_rw.m_cfg.m_had_nested_quantifiers = false;
            m_rw(curr, result);
            curr = result;  
        } while (m_rw.m_cfg.m_had_nested_quantifiers);
    }

public:
    expand_bounded_quantifiers_tactic(ast_manager & m, params_ref const & p):
	m_rw(m, p) {
	    m_params = p;
    }

    virtual tactic * translate(ast_manager & m) {
	return alloc(expand_bounded_quantifiers_tactic, m, m_params);
    }

    virtual ~expand_bounded_quantifiers_tactic() {}

    virtual void updt_params(params_ref const & p) {
	    m_params = p;
	    m_rw.cfg().updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) { 
	expand_bounded_quantifiers_params::collect_param_descrs(r);
    }

    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        TRACE("expand_bounded_quantifiers", tout << "params: " << m_params << "\n"; g->display(tout););
        fail_if_proof_generation("expand_bounded_quantifiers_tactic", g);
        ast_manager & m = g->m();
        SASSERT(g->is_well_sorted());
        mc = 0; pc = 0; core = 0;
        tactic_report report("expand_bounded_quantifiers", *g);
        unsigned sz = g->size();
        //first check for cardinality bounds for sorts
        m_rw.m_cfg.m_cardinality_bounds.reset();
        cardinality_bound_recognizer cbr(m);
        for (unsigned i = 0; i < sz; i++) {
            sort * s;
            ptr_vector<expr> pexpr;
            if (cbr.get_cardinality_bound(g->form(i), s, pexpr)) {
                TRACE("expand_bounded_quantifiers-debug", tout << "Found bound for sort " << mk_pp(s,m);
                                                          tout << ", size = " << pexpr.size() << ", contains = " << m_rw.m_cfg.m_cardinality_bounds.contains(s) << "\n";);
                if (m_rw.m_cfg.m_cardinality_bounds.contains(s)) {
                    //add if a smaller bound
                    if (pexpr.size()<m_rw.m_cfg.m_cardinality_bounds.find(s).size()) {
                        m_rw.m_cfg.m_cardinality_bounds.remove(s);
                        m_rw.m_cfg.m_cardinality_bounds.insert(s, pexpr);
                    }
                }
                else {
                    m_rw.m_cfg.m_cardinality_bounds.insert(s, pexpr);
                }
            }
        }
        for (unsigned i = 0; i < sz; i++) {
            expr * curr = g->form(i);
            expr_ref new_curr(m);
            apply_rewrite(curr, new_curr);
            g->update(i, new_curr, 0, g->dep(i));
        }
        g->inc_depth();
        if (!m_rw.is_precise()) {
            g->updt_prec(goal::UNDER);
        }
        result.push_back(g.get());
        TRACE("expand_bounded_quantifiers", g->display(tout););
        SASSERT(g->is_well_sorted());
    }
    
    virtual void cleanup() {
        m_rw.cleanup();
    }
    
    virtual void set_cancel(bool f) {
        m_rw.set_cancel(f);
    }
};


tactic * mk_expand_bounded_quantifiers_tactic_core(ast_manager & m, params_ref const & p) {
  return alloc(expand_bounded_quantifiers_tactic, m, p);
}

tactic * mk_expand_bounded_quantifiers_tactic(ast_manager & m, params_ref const & p) {
    return and_then(mk_normalize_bounded_quantifiers_tactic(m), 
                    mk_expand_bounded_quantifiers_tactic_core(m,p));
}
