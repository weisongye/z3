/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    propagate_ineqs_tactic.h

Abstract:

    This tactic performs the following tasks:

     - Propagate bounds using the bound_propagator.
     - Eliminate subsumed inequalities.  
       For example:
          x - y >= 3
          can be replaced with true if we know that
          x >= 3 and y <= 0
            
     - Convert inequalities of the form p <= k and p >= k into p = k,
       where p is a polynomial and k is a constant.

    This strategy assumes the input is in arith LHS mode.
    This can be achieved by using option :arith-lhs true in the
    simplifier.
     
Author:

    Leonardo (leonardo) 2012-02-19

Notes:

--*/
#include"tactical.h"
#include"expr_bound_propagator.h"
#include"arith_decl_plugin.h"

class propagate_ineqs_tactic : public tactic {
    struct     imp;
    imp *      m_imp;
    params_ref m_params;
public:
    propagate_ineqs_tactic(ast_manager & m, params_ref const & p);

    virtual tactic * translate(ast_manager & m) {
        return alloc(propagate_ineqs_tactic, m, m_params);
    }

    virtual ~propagate_ineqs_tactic();

    virtual void updt_params(params_ref const & p);
    virtual void collect_param_descrs(param_descrs & r) {}

    virtual void operator()(goal_ref const & g, goal_ref_buffer & result, model_converter_ref & mc, proof_converter_ref & pc, expr_dependency_ref & core);
    
    virtual void cleanup();
protected:
    virtual void set_cancel(bool f);
};

tactic * mk_propagate_ineqs_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(propagate_ineqs_tactic, m, p));
}

struct propagate_ineqs_tactic::imp {
    ast_manager &          m;
    expr_bound_propagator  bp;
    arith_util             m_util;
    goal_ref               m_new_goal;
    
    imp(ast_manager & _m, params_ref const & p):
        m(_m),
        bp(_m),
        m_util(m) {
        updt_params(p);
    }

    void updt_params(params_ref const & p) {
        params_ref p2 = p;
        p2.set_bool("arith_lhs", true);
        bp.updt_params(p2);
    }

    bool collect_bounds(goal const & g) {
        bool found = false;
        unsigned sz = g.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * t = g.form(i);
            if (bp.assert_expr(t))
                found = true;
            else
                m_new_goal->assert_expr(t); // save non-bounds here
        }
        return found;
    }

    bool lower_subsumed(expr * p, mpq const & k, bool strict) {
        expr_bound_propagator::numeral_manager & nm = bp.nm();
        scoped_mpq implied_k(nm);
        bool implied_strict;
        if (!bp.poly_lower(p, implied_k, implied_strict))
            return false;
        return (nm.gt(implied_k, k) || (nm.eq(implied_k, k) && (!strict || implied_strict)));
    }

    bool upper_subsumed(expr * p, mpq const & k, bool strict) {
        expr_bound_propagator::numeral_manager & nm = bp.nm();
        scoped_mpq implied_k(nm);
        bool implied_strict;
        if (!bp.poly_upper(p, implied_k, implied_strict))
            return false;
        return (nm.lt(implied_k, k) || (nm.eq(implied_k, k) && (!strict || implied_strict)));
    }
    
    void restore_bounds() {
        expr_bound_propagator::numeral_manager & nm = bp.nm();
        scoped_mpq l(nm), u(nm);
        bool strict_l, strict_u, has_l, has_u;
        unsigned sz = bp.num_exprs();
        for (unsigned i = 0; i < sz; i++) {
            expr * p = bp.get_expr(i);
            has_l = bp.lower(p, l, strict_l);
            has_u = bp.upper(p, u, strict_u);
            if (!has_l && !has_u)
                continue;
            if (has_l && has_u && nm.eq(l, u) && !strict_l && !strict_u) {
                // l <= p <= l -->  p = l
                m_new_goal->assert_expr(m.mk_eq(p, m_util.mk_numeral(rational(l), m_util.is_int(p))));
                continue;
            }
            if (has_l && !lower_subsumed(p, l, strict_l)) {
                if (strict_l)
                    m_new_goal->assert_expr(m.mk_not(m_util.mk_le(p, m_util.mk_numeral(rational(l), m_util.is_int(p)))));
                else
                    m_new_goal->assert_expr(m_util.mk_ge(p, m_util.mk_numeral(rational(l), m_util.is_int(p))));
            }
            if (has_u && !upper_subsumed(p, u, strict_u)) {
                if (strict_u)
                    m_new_goal->assert_expr(m.mk_not(m_util.mk_ge(p, m_util.mk_numeral(rational(u), m_util.is_int(p)))));
                else
                    m_new_goal->assert_expr(m_util.mk_le(p, m_util.mk_numeral(rational(u), m_util.is_int(p))));
            }
        }
    }

    void operator()(goal * g, goal_ref & r) {
        tactic_report report("propagate-ineqs", *g);

        m_new_goal = alloc(goal, *g, true);
        m_new_goal->inc_depth();
        r = m_new_goal.get();
        if (!collect_bounds(*g)) {
            m_new_goal = 0;
            r = g;
            return; // nothing to be done
        }
        
        TRACE("propagate_ineqs_tactic", g->display(tout); bp.display(tout); tout << "bound propagator:\n"; bp.display(tout););

        bp.propagate();

        // report_tactic_progress(":bound-propagations", bp.get_num_propagations());
        // report_tactic_progress(":bound-false-alarms", bp.get_num_false_alarms());

        if (bp.inconsistent()) {
            r->reset();
            r->assert_expr(m.mk_false());
            return;
        }

        restore_bounds();
        
        TRACE("propagate_ineqs_tactic", tout << "after propagation:\n"; bp.display(tout); bp.display(tout););
        TRACE("propagate_ineqs_tactic", r->display(tout););
    }

    void set_cancel(bool f) {
        bp.set_cancel(f);
    }
};

propagate_ineqs_tactic::propagate_ineqs_tactic(ast_manager & m, params_ref const & p):
    m_params(p) {
    m_imp = alloc(imp, m, p);
}

propagate_ineqs_tactic::~propagate_ineqs_tactic() {
    dealloc(m_imp);
}

void propagate_ineqs_tactic::updt_params(params_ref const & p) {
    m_params = p;
    m_imp->updt_params(p);
}

void propagate_ineqs_tactic::operator()(goal_ref const & g, 
                                        goal_ref_buffer & result, 
                                        model_converter_ref & mc, 
                                        proof_converter_ref & pc,
                                        expr_dependency_ref & core) {
    SASSERT(g->is_well_sorted());
    fail_if_proof_generation("propagate-ineqs", g);
    fail_if_unsat_core_generation("propagate-ineqs", g);
    mc = 0; pc = 0; core = 0; result.reset();
    goal_ref r;
    (*m_imp)(g.get(), r);
    result.push_back(r.get());
    SASSERT(r->is_well_sorted());
}

void propagate_ineqs_tactic::set_cancel(bool f) {
    if (m_imp)
        m_imp->set_cancel(f);
}
 
void propagate_ineqs_tactic::cleanup() {
    ast_manager & m = m_imp->m;
    imp * d = m_imp;
    #pragma omp critical (tactic_cancel)
    {
        d = m_imp;
    }
    dealloc(d);
    d = alloc(imp, m, m_params);
    #pragma omp critical (tactic_cancel) 
    {
        m_imp = d;
    }
}
