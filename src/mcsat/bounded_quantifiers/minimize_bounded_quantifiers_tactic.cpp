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
#include"expr_bound_propagator.h"
#include"ast_pp.h"
#include"normalize_bounded_quantifiers_tactic.h"
#include"assertion_stream.h"
#include"simplify_tactic.h"
#include"nnf_tactic.h"

class minimize_bounded_quantifiers_tactic : public tactic {
    struct rw_cfg : public default_rewriter_cfg {
        ast_manager &          m_m;
        expr_bound_propagator  m_bp;
        arith_util             m_autil;
        
        rw_cfg(ast_manager & m, params_ref const & p):m_m(m), m_bp(m, p), m_autil(m) {
        }
        
        void updt_params(params_ref const & p) {
            m_bp.updt_params(p);
        }

        bool has_int_var(quantifier * q) {
            for (unsigned i = 0; i < q->get_num_decls(); i++) {
                if (m_autil.is_int(q->get_decl_sort(i)))
                    return true;
            }
            return false;
        }

        bool reduce_quantifier(quantifier * old_q, 
                               expr * new_body, 
                               expr * const * new_patterns, 
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {
            if (!old_q->is_forall() || !m_m.is_or(new_body) || !has_int_var(old_q))
                return false;
            quantifier_ref  q(m_m);
            m_bp.push();
            expr_ref_buffer new_lits(m_m);
            expr_ref not_l(m_m);
            for (unsigned i = 0; i < to_app(new_body)->get_num_args(); i++) {
                expr * l = to_app(new_body)->get_arg(i);
                if (m_m.is_not(l))
                    not_l = to_app(l)->get_arg(0);
                else
                    not_l = m_m.mk_not(l);
                m_bp.assert_expr(not_l);
                new_lits.push_back(l);
            }
            m_bp.propagate();
            TRACE("minimize_bounded_quantifiers", tout << "new_body:\n" << mk_pp(new_body, m_m) << "\nbounds:\n"; m_bp.display(tout););
            if (m_bp.inconsistent()) {
                m_bp.pop(1);
                result = m_m.mk_true();
                return true;
            }
            else {
                // collect new bounds
                unsigned num_vars = old_q->get_num_decls();
                expr_ref x(m_m);
                expr_ref new_ineq(m_m);
                bool found = false;
                for (unsigned i = 0; i < num_vars; i++) {
                    sort * s = old_q->get_decl_sort(num_vars - i - 1);
                    if (m_autil.is_int(s)) {
                        x = m_m.mk_var(i, s);
                        if (m_bp.get_lower_ineq(x, new_ineq)) {
                            new_lits.push_back(m_m.mk_not(new_ineq));
                            found = true;
                        }
                        if (m_bp.get_upper_ineq(x, new_ineq)) {
                            new_lits.push_back(m_m.mk_not(new_ineq));
                            found = true;
                        }
                    }
                }
                m_bp.pop(1);
                if (!found)
                    return false;
                result = m_m.update_quantifier(old_q, old_q->get_num_patterns(), new_patterns, old_q->get_num_no_patterns(), new_no_patterns, 
                                               m_m.mk_or(new_lits.size(), new_lits.c_ptr()));
                return true;
            }
        }
    };
    
    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;
        rw(ast_manager & m, params_ref const & p):
            rewriter_tpl<rw_cfg>(m, false, m_cfg),
            m_cfg(m, p) {
        }
    };

   
    rw            m_rw;
    params_ref    m_params;

    bool init_bounds(assertion_stream & g) {
        expr_bound_propagator & bp = m_rw.cfg().m_bp;
        bp.reset();
        if (m_params.get_bool("global", true)) {
            unsigned sz = g.size();
            for (unsigned i = 0; i < sz; i++) {
                bp.assert_expr(g.form(i));
            }
            bp.propagate();
            if (bp.inconsistent()) {
                g.assert_expr(g.m().mk_false());
                return false;
            }
        }
        return true;
    }
    
    void apply(assertion_stream & g) {
        TRACE("minimize_bounded_quantifiers", g.display(tout););
        fail_if_proof_generation("minimize_bounded_quantifiers_tactic", g.proofs_enabled());
        ast_manager & m = g.m();
        SASSERT(g.is_well_sorted());
        if (!init_bounds(g))
            return;
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

public:
    minimize_bounded_quantifiers_tactic(ast_manager & m, params_ref const & p):
	m_rw(m, p),
	m_params(p) {
    }

    virtual tactic * translate(ast_manager & m) {
	return alloc(minimize_bounded_quantifiers_tactic, m, m_params);
    }

    virtual ~minimize_bounded_quantifiers_tactic() {}

    virtual void updt_params(params_ref const & p) { 
        m_params = p; 
        m_rw.cfg().updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) { 
        r.insert("global", CPK_BOOL, "Use global bound propagation (default: true)");
        m_rw.cfg().m_bp.get_param_descrs(r);
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
        m_rw.cfg().m_bp.reset();
    }
    
    virtual void set_cancel(bool f) {
        m_rw.set_cancel(f);
        m_rw.cfg().m_bp.set_cancel(f);
    }
};

tactic * mk_minimize_bounded_quantifiers_tactic_core(ast_manager & m, params_ref const & p) {
    return alloc(minimize_bounded_quantifiers_tactic, m, p);
}

tactic * mk_minimize_bounded_quantifiers_tactic(ast_manager & m, params_ref const & p) {
    params_ref np;
    np.set_bool("skolemize", false);
    np.set_bool("ignore_nested", true);
    np.set_sym("mode", symbol("quantifiers"));
    params_ref sp;
    sp.set_bool("arith_lhs", true);
    return and_then(using_params(mk_nnf_tactic(m), np),
                    using_params(mk_simplify_tactic(m), sp),
                    mk_minimize_bounded_quantifiers_tactic_core(m, p),
                    mk_simplify_tactic(m));
}

