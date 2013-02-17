/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    elim_patterns_tactic.cpp

Abstract:

    Eliminate pattern annotations in the code.

Author:

    Leonardo de Moura (leonardo) 2013-02-17.

--*/
#include"tactical.h"
#include"rewriter_def.h"
#include"assertion_stream.h"

class elim_patterns_tactic : public tactic {

    struct rw_cfg : public default_rewriter_cfg {
        ast_manager & m;

        rw_cfg(ast_manager & _m):m(_m) {
        }

        bool reduce_quantifier(quantifier * old_q, 
                               expr * new_body, 
                               expr * const * new_patterns, 
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {
            if (old_q->get_num_patterns() > 0 || old_q->get_num_no_patterns() > 0) {
                result = m.update_quantifier(old_q, 0, 0, 0, 0, new_body);
                return true;
            }
            else {
                return false;
            }
        }
    };

    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;
        
        rw(ast_manager & m, bool proofs_enabled):
            rewriter_tpl<rw_cfg>(m, proofs_enabled, m_cfg),
            m_cfg(m) {
        }
    };

    rw *  m_rw;

    struct set_rw {
        elim_patterns_tactic & m;
        set_rw(elim_patterns_tactic & _m, rw & r):m(_m) {
            #pragma omp critical (tactic_cancel)
            {
                m.m_rw  = &r;
            }
        }
        ~set_rw() {
            #pragma omp critical (tactic_cancel)
            {
                m.m_rw  = 0;
            }
        }
    };

    void apply(assertion_stream & g) {
        SASSERT(g.is_well_sorted());
        ast_manager & m = g.m();
        stream_report report("elim_patterns", g);
        bool produce_proofs = g.proofs_enabled();

        rw r(m, produce_proofs);
        set_rw s(*this, r);

        expr_ref   new_curr(m);
        proof_ref  new_pr(m);
        unsigned size = g.size();
        for (unsigned idx = g.qhead(); idx < size; idx++) {
            if (g.inconsistent())
                break;
            expr * curr = g.form(idx);
            r(curr, new_curr, new_pr);
            if (g.proofs_enabled()) {
                proof * pr = g.pr(idx);
                new_pr    = m.mk_modus_ponens(pr, new_pr);
            }
            g.update(idx, new_curr, new_pr, g.dep(idx));
        }
        TRACE("elim_patterns", g.display(tout););
        SASSERT(g.is_well_sorted());
    }

public:
    elim_patterns_tactic():m_rw(0) {}

    virtual tactic * translate(ast_manager & m) {
        return alloc(elim_patterns_tactic);
    }

    virtual void updt_params(params_ref const & p) {}
    virtual void collect_param_descrs(param_descrs & r) {}
    
    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        mc = 0; pc = 0; core = 0; result.reset();
        goal2stream s(*(g.get()));
        apply(s);
        g->inc_depth();
        result.push_back(g.get());
    }

    virtual void operator()(assertion_stack & s) {
        assertion_stack2stream strm(s);
        apply(strm);
    }
                            
    virtual void set_cancel(bool f) {
        if (m_rw)
            m_rw->set_cancel(f);
    }

    virtual void cleanup() {}
};

tactic * mk_elim_patterns_tactic(ast_manager & m, params_ref const & p) {
    return alloc(elim_patterns_tactic);
}
