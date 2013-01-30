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
#include"bounded_quantifiers_tactic.h"
#include"tactic.h"
#include"rewriter_def.h"
#include"var_subst.h"
#include"bound_info.h"
#include"ast_pp.h"
#include"th_rewriter.h"
#include"bound_minimize.h"
#include"bounded_quantifiers_params.hpp"
#include"assertion_stream.h"

class normalize_bounded_quantifiers_tactic : public tactic {

    struct rw_cfg : public default_rewriter_cfg {
        ast_manager & m;
        arith_util m_au;
        bv_util m_bvu;
        datatype_util m_dtu;
        rw_cfg(ast_manager & _m):m(_m), m_au(m), m_bvu(m), m_dtu(m){}
        
        bool reduce_quantifier(quantifier * old_q, 
                               expr * new_body, 
                               expr * const * new_patterns, 
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {
            TRACE("normalize_bounded_quantifiers",tout << "Process " << mk_pp(old_q,m) << "\n";);
            quantifier * q = m.update_quantifier(old_q, old_q->get_num_patterns(), new_patterns, old_q->get_num_no_patterns(), new_no_patterns, new_body);
            bound_info bi(m, m_au, m_bvu, m_dtu, q);
            if (bi.compute()) {
                //bi.print("normalize_bounded_quantifiers-debug");
                expr_ref_buffer bound_lits(m);
                expr_ref_buffer body_lits(m);
                //start with all literals from body
                body_lits.append(bi.m_body.size(), bi.m_body.c_ptr());
                //make the substitution we will be using
                expr_ref_buffer subs(m);
                for (unsigned i=0; i<q->get_num_decls(); i++) {
                    sort * s = q->get_decl_sort(i);
                    expr * v = m.mk_var(q->get_num_decls()-1-i, s);
                    subs.push_back(v);
                }
                //substitution object
                var_subst vs(m);
                //normalize each of the bounds
                for (unsigned iv=0; iv<bi.m_var_order.size(); iv++) {
                    unsigned i = bi.m_var_order[iv];
                    sort * s = q->get_decl_sort(q->get_num_decls()-1-i);
                    expr * v = m.mk_var(i, s);
                    //construct lower and upper bounds (must apply current substitution to them)
                    expr_ref lower(m);
                    expr_ref upper(m);
                    vs(bi.get_lower_bound(i), subs.size(), subs.c_ptr(), lower);
                    vs(bi.get_upper_bound(i), subs.size(), subs.c_ptr(), upper);
                    expr_ref subs_val(m);
                    //add normalized bounds to bound_lits
                    if (m_au.is_int(s)) {
                        bound_lits.push_back(m.mk_not(m_au.mk_ge(v, m_au.mk_numeral(rational(0), true))));
                        if (bi.is_normalized(i)) {
                            bound_lits.push_back(m.mk_not(m_au.mk_le(v, upper)));
                            subs_val = v;
                        }
                        else {
                            bound_lits.push_back(m.mk_not(m_au.mk_le(v, m_au.mk_sub(upper, lower))));
                            subs_val = m_au.mk_add(v, lower);
                        }
                    }
                    else if (m_bvu.is_bv_sort(s)) {
                        unsigned sz = m_bvu.get_bv_size(s);
                        bound_lits.push_back(m.mk_not(m_bvu.mk_ule(m_bvu.mk_numeral(rational(0), sz),v)));
                        if (bi.is_normalized(i)) {
                            bound_lits.push_back(m.mk_not(m_bvu.mk_ule(v,upper)));
                            subs_val = v;
                        }
                        else {
                            bound_lits.push_back(m.mk_not(m_bvu.mk_ule(v, m_bvu.mk_bv_sub(upper, lower))));
                            //additionally, body is satisfied when lower > upper
                            bound_lits.push_back(m.mk_not(bi.is_bv_signed_bound(i) ? m_bvu.mk_sle(lower, upper) :
                                                          m_bvu.mk_ule(lower, upper)));
                            subs_val = m_bvu.mk_bv_add(v, lower);
                        }
                    }
                    //also add v -> (v+l) to the substitution
                    TRACE("normalize_bounded_quantifiers-debug",tout << "Substitution value for variable " << i << " is " << mk_pp(subs_val,m) << "\n";);
                    subs.setx(q->get_num_decls()-1-i, subs_val);
                }
                //apply substitution to each of the body literals
                for (unsigned i = 0; i < body_lits.size(); i++) {
                    expr_ref bd_res(m);
                    vs(body_lits[i], subs.size(), subs.c_ptr(), bd_res);
                    body_lits.setx(i, bd_res);
                }
                //construct the body (it is an "or" of all the literals)
                bound_lits.append(body_lits.size(), body_lits.c_ptr());
                result = m.update_quantifier(q, m.mk_or(bound_lits.size(), bound_lits.c_ptr()));
                TRACE("normalize_bounded_quantifiers",tout << "Normalized " << mk_pp(old_q,m) << " to \n     " << mk_pp(result,m) << "\n";);
                return true;
            }
            else {
                TRACE("normalize_bounded_quantifiers",tout << "Could not find bounds.\n";);
            }
            
            return false;
        }
    };

    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;
        rw(ast_manager & m):
            rewriter_tpl<rw_cfg>(m, false, m_cfg),
            m_cfg(m) {
        }
    };

    rw m_rw;

public:
    normalize_bounded_quantifiers_tactic(ast_manager & m):
        m_rw(m) {
    }

    virtual tactic * translate(ast_manager & m) {
	return alloc(normalize_bounded_quantifiers_tactic, m);
    }

    virtual ~normalize_bounded_quantifiers_tactic() {}

    virtual void updt_params(params_ref const & p) {}

    virtual void collect_param_descrs(param_descrs & r) {}

    void apply(assertion_stream & g) {
        TRACE("normalize_bounded_quantifiers", g.display(tout););
        fail_if_proof_generation("normalize_bounded_quantifiers", g.proofs_enabled());
        stream_report report("normalize_bounded_quantifiers", g);
        ast_manager & m = g.m();
        SASSERT(g.is_well_sorted());
        unsigned sz = g.size();
        expr_ref new_curr(m);
        for (unsigned i = g.qhead(); i < sz; i++) {
            expr * curr = g.form(i);
            m_rw(curr, new_curr);
            g.update(i, new_curr, 0, g.dep(i));
        }
        TRACE("normalize_bounded_quantifiers", g.display(tout););
        SASSERT(g.is_well_sorted());
    }

    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        mc = 0; pc = 0; core = 0;
        goal2stream s(*(g.get()));
        apply(s);
        g->inc_depth();
        result.push_back(g.get());
    }

    virtual void operator()(assertion_stack & s) {
        assertion_stack2stream strm(s);
        apply(strm);
    }
    
    virtual void cleanup() {
        m_rw.cleanup();
    }

    virtual void set_cancel(bool f) {
        m_rw.set_cancel(f);
    }
};


tactic * mk_normalize_bounded_quantifiers_tactic(ast_manager & m) {
  return alloc(normalize_bounded_quantifiers_tactic, m);
}

class minimize_bounded_quantifiers_tactic : public tactic {
    struct rw_cfg : public default_rewriter_cfg {
        ast_manager & m_m;
        arith_util m_au;
        bv_util m_bvu;
        datatype_util m_dtu;
        bound_propagator::numeral_manager m_nm;
        bound_propagator::allocator m_alloc;
        params_ref m_arith_p;
        th_rewriter m_arith_simp;
        rw_cfg(ast_manager & _m):m_m(_m), m_au(_m), m_bvu(_m), m_dtu(_m), m_arith_simp(_m,m_arith_p){
            m_arith_p.set_bool("sort_sums", true);
            m_arith_p.set_bool("ule-split", false);
        }
        
        bool reduce_quantifier(quantifier * old_q, 
                               expr * new_body, 
                               expr * const * new_patterns, 
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {
            TRACE("minimize_bounded_quantifiers",tout << "Process " << mk_pp(old_q,m_m) << "\n";);
            quantifier * q = m_m.update_quantifier(old_q, old_q->get_num_patterns(), new_patterns, old_q->get_num_no_patterns(), new_no_patterns, new_body);
            bound_info bi(m_m, m_au, m_bvu, m_dtu, q);
            if (bi.compute()) {
                bi.print("minimize_bounded_quantifiers");
                //must rewrite the bounds
                bi.apply_rewrite(m_arith_simp);
                propagate_bound_info pbi(m_m, m_au, m_nm, m_alloc);
                if (pbi.compute(bi)) {
                    if (bi.is_trivial_sat()) {
                        //bound were found to be inconsistent
                        result = m_m.mk_true();
                        TRACE("minimize_bounded_quantifiers",tout  << "Incosistent bounds, discard quantified formula.\n";);
                        return true;
                    }
                    else {
                        result = bi.get_quantifier();
                        TRACE("minimize_bounded_quantifiers",tout  << "After bound propagations : " << mk_pp(result,m_m) << "\n";);
                        return true;
                    }
                }
            }
            return false;
        }
    };
    
    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;
        rw(ast_manager & m):
            rewriter_tpl<rw_cfg>(m, false, m_cfg),
            m_cfg(m) {
        }
    };
    
    rw            m_rw;
    params_ref    m_params;

public:
    minimize_bounded_quantifiers_tactic(ast_manager & m, params_ref const & p):
	m_rw(m),
	m_params(p) {
    }

    virtual tactic * translate(ast_manager & m) {
	return alloc(minimize_bounded_quantifiers_tactic, m, m_params);
    }

    virtual ~minimize_bounded_quantifiers_tactic() {}

    virtual void updt_params(params_ref const & p) { m_params = p; }

    virtual void collect_param_descrs(param_descrs & r) { }

    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        TRACE("minimize_bounded_quantifiers", tout << "params: " << m_params << "\n"; g->display(tout););
        fail_if_proof_generation("minimize_bounded_quantifiers_tactic", g);
        ast_manager & m = g->m();
        SASSERT(g->is_well_sorted());
        mc = 0; pc = 0; core = 0;
        tactic_report report("minimize_bounded_quantifiers", *g);
        unsigned sz = g->size();
	    expr_ref new_curr(m);
        for (unsigned i = 0; i < sz; i++) {
            expr * curr = g->form(i);
	        m_rw(curr, new_curr);
            g->update(i, new_curr, 0, g->dep(i));
        }
        g->inc_depth();
        result.push_back(g.get());
        TRACE("minimize_bounded_quantifiers", g->display(tout););
        SASSERT(g->is_well_sorted());
    }
    
    virtual void cleanup() {
	    m_rw.cleanup();
    }

    virtual void set_cancel(bool f) {
	    m_rw.set_cancel(f);
    }
};

tactic * mk_minimize_bounded_quantifiers_tactic_core(ast_manager & m, params_ref const & p) {
  return alloc(minimize_bounded_quantifiers_tactic, m, p);
}

tactic * mk_minimize_bounded_quantifiers_tactic(ast_manager & m, params_ref const & p) {
  return and_then(mk_normalize_bounded_quantifiers_tactic(m), mk_minimize_bounded_quantifiers_tactic_core(m,p));
}


//expand tactic
// parameters should take:
//    int expand_bound:         what bound we should try for integers, bit-vectors
//    int exp_bound_limit:      if bound is already known to be 0 <= x <= n for some variable x and value n, and if n>exp_bound_limit, we fail.
class expand_bounded_quantifiers_tactic : public tactic {

    struct rw_cfg : public default_rewriter_cfg {
        
        bool process(bound_info & bi, unsigned index, expr_ref_buffer & val_subs, expr_ref_buffer & exp_result) {
            if (index == bi.m_var_order.size()) {
                if (m_inst_count>=m_exp_bound_inst_limit) {
                    return false;
                }
                else {
                    m_inst_count++;
                    //add body substituted for the values in vals
                    expr_ref subs_body(m);
                    instantiate(m, bi.m_q, val_subs.c_ptr(), subs_body);
                    arith_simp(subs_body,subs_body);
                    exp_result.push_back(subs_body);
                    return true;
                }
            }
            else {
                unsigned i = bi.m_var_order[index];
                sort * s = bi.m_q->get_decl_sort(bi.m_q->get_num_decls()-1-i);
                //calculate the range
                expr_ref upper(m);
                upper = bi.get_upper_bound(i);
                //apply substitution to "upper" based on val_subs
                SASSERT(bi.m_q->get_num_decls() == val_subs.size());
                instantiate(m, upper, val_subs.size(), val_subs.c_ptr(), upper);
                //rewrite upper?
                arith_simp(upper,upper);
                //find the constant range
                rational range;
                bool success = false;
                if (m_au.is_int(s)) {
                    if (m_au.is_numeral(upper, range)) {
                        //the range is already a constant
                        success = true;
                    }
                    else {
                        //the range is the bound we have specified
                        range = rational(m_exp_bound - 1);  // minus one since we have a non-strict lower bound of zero
                        //must add constraint to result to make it constant
                        expr_ref bnd(m);
                        bnd = m_au.mk_le(upper, m_au.mk_numeral(range, true));
                        TRACE("expand_bounded_quantifiers-debug", tout << "Add symbolic constraint " << mk_pp(bnd,m) << "\n";);
                        if (!exp_result.contains(bnd)) {
                            m_precise = false;
                            exp_result.push_back(bnd);
                        }
                        success = true;
                    }
                }
                else if (m_bvu.is_bv_sort(s)) {
                    unsigned sz;
                    if (m_bvu.is_numeral(upper, range, sz)) {
                        success = true;
                    }
                    else {
                        range = rational(m_exp_bound - 1); //minus one since we have a non-strict lower bound of zero
                        //must add constraint to result to make it constant
                        expr_ref bnd(m);
                        bnd = m_bvu.mk_ule(upper, m_bvu.mk_numeral(range, s));
                        if (!exp_result.contains(bnd)) {
                            m_precise = false;
                            exp_result.push_back(bnd);
                        }
                        success = true;
                    }
                }
                //if we found a range and it is less than our bound limit
                if (success) {
                    if (range.is_nonneg()) {
                        if (!range.is_uint64() || range.get_uint64() > UINT_MAX)
                            return false;
                        unsigned _range = static_cast<unsigned>(range.get_uint64());
                        //iterate over all values in the range
                        for (unsigned v = 0; v <= _range; v++) {
                            expr_ref val(m);
                            val = m_au.is_int(s) ? m_au.mk_numeral(rational(v), true) : m_bvu.mk_numeral(rational(v),s);
                            val_subs.setx(bi.m_q->get_num_decls() - 1 - i, val);
                            TRACE("expand_bounded_quantifiers-debug", tout << "Consider " << v << " / " << i << "\n";);
                            //check if the body is trivially satisfied?
                            if (!process(bi, index+1, val_subs, exp_result)) {
                                return false;
                            }
                        }
                    }
                    return true;
                }
                else {
                    TRACE("expand_bounded_quantifiers", tout << "Could not process upper bound " << mk_pp(upper,m) << "\n";);
                    return false;
                }
            }
        }

    public:
        ast_manager & m;
        arith_util m_au;
        bv_util m_bvu;
        datatype_util m_dtu;
        unsigned m_exp_bound;
        unsigned m_exp_bound_inst_limit;
        unsigned m_inst_count;
        params_ref arith_p;
        th_rewriter arith_simp;
        bool m_precise;

        rw_cfg(ast_manager & _m, params_ref const & p):
            m(_m), m_au(m), m_bvu(m), m_dtu(m), arith_simp(m,arith_p){
            arith_p.set_bool("sort_sums", true);
            arith_p.set_bool("ule-split", false);
            m_inst_count = 0;
            m_precise = true;
	    updt_params(p);
        }

	void updt_params(params_ref const & _p) {
	    bounded_quantifiers_params p(_p);
	    m_exp_bound            = p.domain();
	    m_exp_bound_inst_limit = p.max_instances();
	}

        bool reduce_quantifier(quantifier * old_q, 
                               expr * new_body, 
                               expr * const * new_patterns, 
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {
            TRACE("expand_bounded_quantifiers", tout << "Process " << mk_pp(old_q,m) << "\n";);
            quantifier_ref q(m);
            q = m.update_quantifier(old_q, old_q->get_num_patterns(), new_patterns, old_q->get_num_no_patterns(), new_no_patterns, new_body);
            bound_info bi(m, m_au, m_bvu, m_dtu, q);
            if (bi.compute()) {
                //check that all lower bounds are zero
                if (bi.is_normalized()) {
                    bi.print("expand_bounded_quantifiers-debug");
                    //we will rewrite the quantifier into a conjunction based on expansion
                    //the values we make for each variable
                    expr_ref_buffer val_subs(m);
                    for (unsigned i=0; i<q->get_num_decls(); i++) {
                        sort * s = q->get_decl_sort(i);
                        expr * v = m.mk_var(q->get_num_decls()-1-i, s);
                        val_subs.push_back(v);
                    }
                    //simplify the new body of quantifier
                    expr_ref body(m);
                    body = q->get_expr();
                    arith_simp(body,body);
                    bi.m_q = m.update_quantifier(q,body);
                    //conjunction of formulas in the result
                    expr_ref_buffer exp_result(m);
                    //now, populate the result buffer
                    m_inst_count = 0;
                    if (process(bi, 0, val_subs, exp_result)) {
                        //result is a conjunction of the literals in exp_result
                        result = exp_result.size()>1 ? m.mk_and(exp_result.size(), exp_result.c_ptr()) : (exp_result.size()==1 ? exp_result[0] : m.mk_true());
                        TRACE("expand_bounded_quantifiers", tout << "Expand, got result " << mk_pp(result,m) << "\n";);
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
            return false;
        }
    };

    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;
        rw(ast_manager & m, params_ref const & p):
            rewriter_tpl<rw_cfg>(m, false, m_cfg),
            m_cfg(m, p) {
        }
        bool is_precise() { return m_cfg.m_precise; }
    };

    rw            m_rw;
    params_ref    m_params;

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
	bounded_quantifiers_params::collect_param_descrs(r);
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
        expr_ref new_curr(m);
        for (unsigned i = 0; i < sz; i++) {
            expr * curr = g->form(i);
            m_rw(curr, new_curr);
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
  return and_then(mk_normalize_bounded_quantifiers_tactic(m), mk_expand_bounded_quantifiers_tactic_core(m,p));
}
