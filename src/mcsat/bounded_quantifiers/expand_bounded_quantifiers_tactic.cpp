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

//expand tactic
// parameters should take:
//    int expand_bound:         what domain size we should try for integers, bit-vectors variables
//    int exp_bound_limit:      if bound is already known to be 0 <= x <= n for some variable x and value n, and if n>exp_bound_limit, we fail.
class expand_bounded_quantifiers_tactic : public tactic {

    struct rw_cfg : public default_rewriter_cfg {
        
        bool process(bound_info & bi, unsigned index, expr_ref_buffer & val_subs, expr_ref_buffer & exp_result) {
            if (index == bi.m_var_order.size()) {
                if (m_inst_count >= m_exp_bound_inst_limit) {
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
        unsigned m_exp_bound;
        unsigned m_exp_bound_inst_limit;
        unsigned m_inst_count;
        th_rewriter arith_simp;
        bool m_precise;

        rw_cfg(ast_manager & _m, params_ref const & p):
            m(_m), m_au(m), m_bvu(m), arith_simp(m){
            params_ref arith_p;
            arith_p.set_bool("sort_sums", true);
            arith_p.set_bool("ule-split", false);
            arith_simp.updt_params(arith_p);
            m_inst_count = 0;
            m_precise = true;
	    updt_params(p);
        }

        void updt_params(params_ref const & _p) {
            expand_bounded_quantifiers_params p(_p);
            m_exp_bound            = p.domain();
            m_exp_bound_inst_limit = p.max_instances();
        }
        
        bool reduce_quantifier(quantifier * old_q, 
                               expr * new_body, 
                               expr * const * new_patterns, 
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {
            quantifier_ref q(m);
            q = m.update_quantifier(old_q, old_q->get_num_patterns(), new_patterns, old_q->get_num_no_patterns(), new_no_patterns, new_body);
            TRACE("expand_bounded_quantifiers", tout << "Process " << mk_pp(q,m) << "\n";);
            bound_info bi(m, m_au, m_bvu, q);
            if (bi.compute()) {
                //check that all lower bounds are zero
                if (bi.is_normalized()) {
                    bi.print("expand_bounded_quantifiers-debug");
                    //we will rewrite the quantifier into a conjunction based on expansion
                    //the values we make for each variable
                    expr_ref_buffer val_subs(m);
                    for (unsigned i = 0; i < q->get_num_decls(); i++) {
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
                        result = mk_and(m, exp_result.size(), exp_result.c_ptr());
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
    return and_then(mk_normalize_bounded_quantifiers_tactic(m), 
                    mk_expand_bounded_quantifiers_tactic_core(m,p));
}
