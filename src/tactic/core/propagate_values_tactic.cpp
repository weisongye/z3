/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    propagate_values_tactic.cpp

Abstract:

    Propagate values using equalities of the form (= t v) where v is a value,
    and atoms t and (not t)

Author:

    Leonardo de Moura (leonardo) 2011-12-28.

Revision History:

--*/
#include"tactical.h"
#include"propagate_values_tactic.h"
#include"th_rewriter.h"
#include"ast_smt2_pp.h"
#include"expr_substitution.h"
#include"goal_shared_occs.h"
#include"assertion_stream.h"

class propagate_values_tactic : public tactic {
    struct     imp {
        ast_manager &                 m_manager;
        th_rewriter                   m_r;
        scoped_ptr<expr_substitution> m_subst;
        assertion_stream *            m_stream;
        goal_shared_occs              m_occs;
        unsigned                      m_idx;
        unsigned                      m_max_rounds;
        bool                          m_from_qhead;
        bool                          m_modified;
        
        imp(ast_manager & m, params_ref const & p):
            m_manager(m),
            m_r(m, p),
            m_stream(0),
            m_occs(m, true /* track atoms */) {
            updt_params_core(p);
        }

        void updt_params_core(params_ref const & p) {
            m_max_rounds = p.get_uint("max_rounds", 4);
            m_from_qhead = p.get_bool("from_qhead", true);
        }
        
        void updt_params(params_ref const & p) {
            m_r.updt_params(p);
            updt_params_core(p);
        }

        ast_manager & m() const { return m_manager; }
        
        void set_cancel(bool f) {
            m_r.set_cancel(f);
        }
        
        bool is_shared(expr * t) {
            return m_occs.is_shared(t);
        }
        
        bool is_shared_neg(expr * t, expr * & atom) {
            if (!m().is_not(t))
                return false;
            atom = to_app(t)->get_arg(0);
            return is_shared(atom);
        }

        bool is_shared_eq(expr * t, expr * & lhs, expr * & value) {
            if (!m().is_eq(t))
                return false;
            expr * arg1 = to_app(t)->get_arg(0);
            expr * arg2 = to_app(t)->get_arg(1);
            if (m().is_value(arg1) && is_shared(arg2)) {
                lhs   = arg2;
                value = arg1;
                return true;
            }
            if (m().is_value(arg2) && is_shared(arg1)) {
                lhs   = arg1;
                value = arg2;
                return true;
            }
            return false;
        }

        void save_subst(expr * lit, proof * pr, expr_dependency * d) {
            if (is_shared(lit)) {
                m_subst->insert(lit, m().mk_true(), m().mk_iff_true(pr), d);
            }
            expr * atom;
            if (is_shared_neg(lit, atom)) {
                m_subst->insert(atom, m().mk_false(), m().mk_iff_false(pr), d);
            }
            expr * lhs, * value;
            if (is_shared_eq(lit, lhs, value)) {
                TRACE("shallow_context_simplifier_bug", tout << "found eq:\n" << mk_ismt2_pp(lit, m()) << "\n";);
                m_subst->insert(lhs, value, pr, d);
            }
        }
        
        void push_result(expr * new_curr, proof * new_pr) {
            if (m_stream->proofs_enabled()) {
                proof * pr = m_stream->pr(m_idx);
                new_pr     = m().mk_modus_ponens(pr, new_pr);
            }
            
            expr_dependency_ref new_d(m());
            if (m_stream->unsat_core_enabled()) {
                new_d = m_stream->dep(m_idx);
                expr_dependency * used_d = m_r.get_used_dependencies();
                if (used_d != 0) {
                    new_d = m().mk_join(new_d, used_d);
                    m_r.reset_used_dependencies();
                }
            }
            
            m_stream->update(m_idx, new_curr, new_pr, new_d);
            save_subst(new_curr, new_pr, new_d);
        }
        
        void process_current() {
            expr * curr = m_stream->form(m_idx);
            expr_ref   new_curr(m());
            proof_ref  new_pr(m());
            
            if (!m_subst->empty()) {
                m_r(curr, new_curr, new_pr);
            }
            else {
                new_curr = curr;
                if (m().proofs_enabled())
                    new_pr   = m().mk_reflexivity(curr);
            }

            TRACE("shallow_context_simplifier_bug", tout << mk_ismt2_pp(curr, m()) << "\n---->\n" << mk_ismt2_pp(new_curr, m()) << "\n";);
            push_result(new_curr, new_pr);
            if (new_curr != curr)
                m_modified = true;
        }

        void apply_core() {
            stream_report report("propagate-values", *m_stream);
            bool forward   = true;
            expr_ref   new_curr(m());
            proof_ref  new_pr(m());
            unsigned size  = m_stream->size();
            unsigned qhead = m_stream->qhead();
            m_idx          = qhead;
            m_modified     = false;
            unsigned round = 0;

            if (m_stream->inconsistent())
                return;

            m_subst = alloc(expr_substitution, m(), m_stream->unsat_core_enabled(), m_stream->proofs_enabled());
            m_r.set_substitution(m_subst.get());
            m_occs(*m_stream, m_from_qhead);

            if (!m_from_qhead) {
                // fill m_subst if values from 0 to qhead
                // this is only relevant if the stream is an assertion stack
                for (unsigned i = 0; i < qhead; i++) {
                    save_subst(m_stream->form(i), m_stream->pr(i), m_stream->dep(i));
                }
            }
            
            while (true) {
                TRACE("propagate_values", m_stream->display(tout););
                if (forward) {
                    for (; m_idx < size; m_idx++) {
                        process_current();
                        if (m_stream->inconsistent()) 
                            return;
                    }
                    if (m_subst->empty() && !m_modified)
                        return;
                    m_occs(*m_stream);
                    m_idx        = m_stream->size();
                    forward      = false;
                    m_subst->reset();
                    m_r.set_substitution(m_subst.get()); // reset, but keep substitution
                }
                else {
                    while (m_idx > qhead) {
                        m_idx--;
                        process_current();
                        if (m_stream->inconsistent()) 
                            return;
                    }
                    if (!m_modified)
                        return;
                    m_subst->reset();
                    m_r.set_substitution(m_subst.get()); // reset, but keep substitution
                    m_modified   = false;
                    m_occs(*m_stream);
                    m_idx        = qhead;
                    size         = m_stream->size();
                    forward      = true;
                }
                round++;
                if (round >= m_max_rounds)
                    break;
                IF_VERBOSE(100, verbose_stream() << "starting new round, goal size: " << m_stream->num_exprs() << std::endl;);
                TRACE("propgate_values", tout << "round finished\n"; m_stream->display(tout); tout << "\n";);
            }
        }

        void apply(assertion_stream & s) {
            m_stream = &s;
            apply_core();
            m_stream->elim_redundancies();
            m_stream->inc_depth();
            SASSERT(m_stream->is_well_sorted());
            TRACE("propagate_values", m_stream->display(tout););
            m_stream = 0;
        }

        void operator()(goal_ref const & g, 
                        goal_ref_buffer & result, 
                        model_converter_ref & mc, 
                        proof_converter_ref & pc,
                        expr_dependency_ref & core) {
            mc = 0; pc = 0; core = 0;
            goal2stream s(*(g.get()));
            apply(s);
            result.push_back(g.get());
            TRACE("propagate_values_core", g->display_with_dependencies(tout););
        }
    };
    
    imp *      m_imp;
    params_ref m_params;
public:
    propagate_values_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(propagate_values_tactic, m, m_params);
    }
    
    virtual ~propagate_values_tactic() {
        dealloc(m_imp);
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
        m_imp->updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) {
        th_rewriter::get_param_descrs(r);
        r.insert("max_rounds", CPK_UINT, "(default: 2) maximum number of rounds.");
        r.insert("from_qhead", CPK_BOOL, "(default: true) if false, then propagate values using assertions that occur before the queue processing head; it will propagate more, but it may be expensive if a lot of push/pop is used; this parameter is irrelevant for goals since the queue head is always 0.");
    }
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        try {
            (*m_imp)(in, result, mc, pc, core);
        }
        catch (rewriter_exception & ex) {
            throw tactic_exception(ex.msg());
        }
    }

    virtual void operator()(assertion_stack & s) {
        assertion_stack2stream strm(s);
        m_imp->apply(strm);
    }
    
    virtual void cleanup() {
        ast_manager & m = m_imp->m();
        imp * d = m_imp;
        #pragma omp critical (tactic_cancel)
        {
            m_imp = 0;
        }
        dealloc(d);
        d = alloc(imp, m, m_params);
        #pragma omp critical (tactic_cancel)
        {
            m_imp = d;
        }
    }
    
protected:
    virtual void set_cancel(bool f) {
        if (m_imp)
            m_imp->set_cancel(f);
    }
};

tactic * mk_propagate_values_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(propagate_values_tactic, m, p));
}

