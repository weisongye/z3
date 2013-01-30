/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    minimize_bounded_quantifiers_tactic.cpp

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-01-17.

--*/
#include"tactical.h"
#include"rewriter_def.h"
#include"bound_info.h"
#include"bound_minimize.h"
#include"ast_pp.h"
#include"normalize_bounded_quantifiers_tactic.h"
#include"assertion_stream.h"
#include"simplify_tactic.h"

class minimize_bounded_quantifiers_tactic : public tactic {
    struct rw_cfg : public default_rewriter_cfg {
        ast_manager & m_m;
        arith_util m_au;
        bv_util m_bvu;
        bound_propagator::numeral_manager m_nm;
        bound_propagator::allocator m_alloc;
        th_rewriter m_arith_simp; // [Leo]: Do we need this?
        rw_cfg(ast_manager & _m):m_m(_m), m_au(_m), m_bvu(_m), m_arith_simp(_m){
            params_ref arith_p;
            arith_p.set_bool("sort_sums", true);
            arith_p.set_bool("ule-split", false);
            m_arith_simp.updt_params(arith_p);
        }
        
        bool reduce_quantifier(quantifier * old_q, 
                               expr * new_body, 
                               expr * const * new_patterns, 
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {
            quantifier_ref  q(m_m);
            q = m_m.update_quantifier(old_q, old_q->get_num_patterns(), new_patterns, old_q->get_num_no_patterns(), new_no_patterns, new_body);
            TRACE("minimize_bounded_quantifiers",tout << "Process " << mk_pp(q,m_m) << "\n";);
            bound_info bi(m_m, m_au, m_bvu, q);
            if (bi.compute()) {
                bi.print("minimize_bounded_quantifiers");
                //must rewrite the bounds
                bi.apply_rewrite(m_arith_simp); // [Leo]: We should remove this. We can add a simplification pass before minimize.
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

    void apply(assertion_stream & g) {
        TRACE("minimize_bounded_quantifiers", g.display(tout););
        fail_if_proof_generation("minimize_bounded_quantifiers_tactic", g.proofs_enabled());
        ast_manager & m = g.m();
        SASSERT(g.is_well_sorted());
        stream_report report("minimize_bounded_quantifiers", g);
        unsigned sz = g.size();
        expr_ref new_curr(m);
        for (unsigned i = g.qhead(); i < sz; i++) {
            expr * curr = g.form(i);
            m_rw(curr, new_curr);
            g.update(i, new_curr, 0, g.dep(i));
        }
        TRACE("minimize_bounded_quantifiers", g.display(tout););
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

tactic * mk_minimize_bounded_quantifiers_tactic_core(ast_manager & m, params_ref const & p) {
    return alloc(minimize_bounded_quantifiers_tactic, m, p);
}

tactic * mk_minimize_bounded_quantifiers_tactic(ast_manager & m, params_ref const & p) {
    return and_then(mk_normalize_bounded_quantifiers_tactic(m), 
                    mk_minimize_bounded_quantifiers_tactic_core(m, p),
                    mk_simplify_tactic(m));
}

