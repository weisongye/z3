/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    normalize_bounded_quantifiers_tactic.cpp

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-01-17.

--*/
#include"tactical.h"
#include"rewriter_def.h"
#include"var_subst.h"
#include"bound_info.h"
#include"assertion_stream.h"
#include"ast_pp.h"
#include"simplify_tactic.h"
#include"nnf_tactic.h"

class normalize_bounded_quantifiers_tactic : public tactic {

    struct rw_cfg : public default_rewriter_cfg {
        ast_manager & m_m;
        arith_util m_au;
        bv_util m_bvu;
        //returns true if we are finished reducing the quantifier
        bool reduce_quantifier_iter(bound_info & bi, quantifier * q, quantifier_ref & result) {
            bool addedOvfBound = false;
            //bi.print("normalize_bounded_quantifiers-debug");
            expr_ref_buffer bound_lits(m_m);
            expr_ref_buffer body_lits(m_m);
            //start with all literals from body
            body_lits.append(bi.m_body.size(), bi.m_body.c_ptr());
            //make the substitution we will be using
            expr_ref_buffer subs(m_m);
            for (unsigned i=0; i<q->get_num_decls(); i++) {
                sort * s = q->get_decl_sort(i);
                expr * v = m_m.mk_var(q->get_num_decls()-1-i, s);
                subs.push_back(v);
            }
            //substitution object
            var_subst vs(m_m);
            //normalize each of the bounds
            for (unsigned iv=0; iv<bi.m_var_order.size(); iv++) {
                unsigned i = bi.m_var_order[iv];
                sort * s = q->get_decl_sort(q->get_num_decls()-1-i);
                expr * v = m_m.mk_var(i, s);
                //construct lower and upper bounds (must apply current substitution to them)
                expr_ref lower(m_m);
                expr_ref upper(m_m);
                vs(bi.get_lower_bound(i), subs.size(), subs.c_ptr(), lower);
                vs(bi.get_upper_bound(i), subs.size(), subs.c_ptr(), upper);
                expr_ref subs_val(m_m);
                //add normalized bounds to bound_lits
                if (m_au.is_int(s)) {
                    bound_lits.push_back(m_m.mk_not(m_au.mk_ge(v, m_au.mk_numeral(rational(0), true))));
                    if (bi.is_normalized(i)) {
                        bound_lits.push_back(m_m.mk_not(m_au.mk_le(v, upper)));
                        subs_val = v;
                    }
                    else{
                        bound_lits.push_back(m_m.mk_not(m_au.mk_le(v, m_au.mk_sub(upper, lower))));
                        subs_val = m_au.mk_add(v, lower);
                    }
                }
                else if (m_bvu.is_bv_sort(s)) {
                    unsigned sz = m_bvu.get_bv_size(s);
                    if (bi.is_normalized(i)) {
                        bound_lits.push_back(m_m.mk_not(m_bvu.mk_ule(v,upper)));
                        subs_val = v;
                    }
                    else {
                        bound_lits.push_back(m_m.mk_not(m_bvu.mk_ule(v, m_bvu.mk_bv_sub(upper, lower))));
                        //additionally, body is satisfied when lower > upper
                        bound_lits.push_back(m_m.mk_not(bi.is_bv_signed_bound(i) ? m_bvu.mk_sle(lower, upper) :
                                                                                    m_bvu.mk_ule(lower, upper)));
                        subs_val = m_bvu.mk_bv_add(v, lower);
                        addedOvfBound = true;
                    }
                }
                //also add v -> (v+l) to the substitution
                TRACE("normalize_bounded_quantifiers-debug",tout << "Substitution value for variable " << i << " is " << mk_pp(subs_val,m_m) << "\n";);
                subs.setx(q->get_num_decls()-1-i, subs_val);
            }
            //apply substitution to each of the body literals
            for (unsigned i=0; i<body_lits.size(); i++) {
                expr_ref bd_res(m_m);
                vs(body_lits[i], subs.size(), subs.c_ptr(), bd_res);
                body_lits.setx(i, bd_res);
            }
            //construct the body (it is an "or" of all the literals)
            bound_lits.append(body_lits.size(), body_lits.c_ptr());
            result = m_m.update_quantifier(q, m_m.mk_or(bound_lits.size(), bound_lits.c_ptr()));
            TRACE("normalize_bounded_quantifiers",tout << "Normalized to \n     " << mk_pp(result,m_m) << "\n";);
            return addedOvfBound;
        }
    public:
        rw_cfg(ast_manager & _m):m_m(_m), m_au(_m), m_bvu(_m) {}
        
        bool reduce_quantifier(quantifier * old_q, 
                               expr * new_body, 
                               expr * const * new_patterns, 
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {
            quantifier_ref q(m_m);
            q = m_m.update_quantifier(old_q, old_q->get_num_patterns(), new_patterns, old_q->get_num_no_patterns(), new_no_patterns, new_body);
            TRACE("normalize_bounded_quantifiers",tout << "Process " << mk_pp(q,m_m) << "\n";);
            bool recompute = false;
            do{
                bound_info bi(m_m, m_au, m_bvu, q);
                if (bi.compute()) {
                    //compute the normalization, possibly may have to recompute bound
                    recompute = reduce_quantifier_iter(bi, q, q);
                }
                else {
                    TRACE("normalize_bounded_quantifiers",tout << "Could not find bounds.\n";);
                    return false;
                }
            } while (recompute);
            result = q;
            return true;
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

tactic * mk_normalize_bounded_quantifiers_tactic_core(ast_manager & m) {
    return alloc(normalize_bounded_quantifiers_tactic, m);
}

tactic * mk_normalize_bounded_quantifiers_tactic(ast_manager & m) {
    params_ref p;
    p.set_bool("arith_lhs", true);
    p.set_bool("elim_and", true);
    return and_then(using_params(mk_simplify_tactic(m), p),
                    mk_snf_tactic(m),
                    mk_normalize_bounded_quantifiers_tactic_core(m),
                    mk_simplify_tactic(m));
}

