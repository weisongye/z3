/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    miniscope_tactic.cpp

Abstract:

    Miniscoping

Author:

    Leonardo de Moura (leonardo) 2013-01-30.

--*/
#include"tactical.h"
#include"rewriter_def.h"
#include"var_subst.h"
#include"assertion_stream.h"
#include"used_vars.h"
#include"ast_pp.h"
#include"cooperate.h"
#include"miniscope_params.hpp"

class miniscope_tactic : public tactic {

    struct rw_cfg : public default_rewriter_cfg {
        ast_manager & m;

        unsigned m_max_depth;
        unsigned m_max_steps;
        unsigned m_curr_steps;
        bool     m_preserve_patterns;
        volatile bool m_cancel;   

        rw_cfg(ast_manager & _m, params_ref const & _p):m(_m) {
            miniscope_params p(_p);
            m_max_depth         = p.max_depth();
            m_max_steps         = p.max_steps();
            m_preserve_patterns = p.preserve_patterns();
            m_curr_steps        = 0;
            m_cancel            = false;
        }

        void set_cancel(bool f) {
            m_cancel = f;
        }

        void checkpoint() {
            cooperate("miniscope");
            if (m_cancel)
                throw tactic_exception(TACTIC_CANCELED_MSG);
        }
        
        void easy_distribute_apply(bool forall, app * p, unsigned depth, quantifier * q, expr_ref & result) {
            expr_ref_buffer new_args(m);
            expr_ref new_arg(m);
            for (unsigned i = 0; i < p->get_num_args(); i++) {
                apply(forall, p->get_arg(i), depth+1, q, new_arg);
                new_args.push_back(new_arg);
            }
            SASSERT(p->get_num_args() > 1);
            result = m.mk_app(p->get_decl(), new_args.size(), new_args.c_ptr());
        } 
        

        // perm is a permutation of the variables
        // perm[0] is the new variable 0
        // ...
        // perm[perm.size() - 1] is the new variable perm.size() - 1
        void reorder_vars(app * p, sbuffer<unsigned> const & perm, quantifier * q, app_ref & new_p) {
            SASSERT(perm.size() == q->get_num_decls());
            unsigned num_vars = perm.size();
            expr_ref_buffer subst(m);
            unsigned i = num_vars;
            while (i > 0) {
                --i;
                unsigned vidx = perm[i];
                sort *   s    = q->get_decl_sort(num_vars - i - 1);
                subst.push_back(m.mk_var(vidx, s));
            }
            var_subst s(m);
            expr_ref aux(m);
            s(p, subst.size(), subst.c_ptr(), aux);
            new_p = to_app(aux);
        }

        void distribute_apply(bool forall, app * p, unsigned depth, quantifier * q, expr_ref & result) {
            sbuffer<bool>   already_found;
            sbuffer<bool>   keep;
            used_vars       uv;
            unsigned        num_vars = q->get_num_decls();
            already_found.resize(num_vars, false);
            keep.resize(num_vars, false);
            for (unsigned i = 0; i < p->get_num_args(); i++) {
                expr * arg = p->get_arg(i);
                uv(arg);
                for (unsigned j = 0; j < num_vars; j++) {
                    if (uv.contains(j)) {
                        if (already_found[j]) {
                            keep[j] = true;
                        }
                        else {
                            already_found[j] = true;
                        }
                    }
                }
            }
            if (std::find(keep.begin(), keep.end(), false) == keep.end()) {
                // keep all... nothing to be done
                default_apply(forall, p, q, result);
            }
            else if (std::find(keep.begin(), keep.end(), true) == keep.end()) {
                // the sets of used variables are disjoint... this is an easy case
                easy_distribute_apply(forall, p, depth, q, result);
            }
            else if (m_preserve_patterns && (q->get_num_patterns() > 0 || q->get_num_no_patterns() > 0)) {
                default_apply(forall, p, q, result);
            }
            else {
                sbuffer<unsigned> perm;
                sbuffer<symbol>   not_keep_names, keep_names;
                ptr_buffer<sort>  not_keep_sorts, keep_sorts;
                unsigned j = 0;
                perm.resize(num_vars, 0);
                // add first variables we should not keep
                for (unsigned i = 0; i < num_vars; i++) {
                    if (!keep[i]) {
                        perm[i] = j; j++;
                        not_keep_names.push_back(q->get_decl_name(num_vars - i - 1));
                        not_keep_sorts.push_back(q->get_decl_sort(num_vars - i - 1));
                    }
                }
                for (unsigned i = 0; i < num_vars; i++) {
                    if (keep[i]) {
                        perm[i] = j; j++;
                        keep_names.push_back(q->get_decl_name(num_vars - i - 1));
                        keep_sorts.push_back(q->get_decl_sort(num_vars - i - 1));
                    }
                }
                std::reverse(not_keep_names.begin(), not_keep_names.end());
                std::reverse(not_keep_sorts.begin(), not_keep_sorts.end());
                std::reverse(keep_names.begin(), keep_names.end());
                std::reverse(keep_sorts.begin(), keep_sorts.end());
                SASSERT(perm.size() == num_vars);
                app_ref new_p(m);
                reorder_vars(p, perm, q, new_p);
                TRACE("miniscope_detail",
                      tout << "perm:"; for (unsigned i = 0; i < perm.size(); i++) tout << " " << perm[i]; tout << "\n";
                      tout << "before reorder:\n" << mk_pp(p, m) << "\n---->\n" << mk_pp(new_p, m) << "\n";);
                quantifier_ref new_q(m);
                new_q = m.mk_quantifier(forall, not_keep_sorts.size(), not_keep_sorts.c_ptr(), not_keep_names.c_ptr(), new_p,
                                        q->get_weight(), q->get_qid(), q->get_skid());
                expr_ref_buffer new_args(m);
                expr_ref new_arg(m);
                for (unsigned i = 0; i < new_p->get_num_args(); i++) {
                    apply(forall, new_p->get_arg(i), depth+1, new_q, new_arg);
                    new_args.push_back(new_arg);
                }
                new_p = m.mk_app(new_p->get_decl(), new_args.size(), new_args.c_ptr());
                result = m.mk_quantifier(forall, keep_sorts.size(), keep_sorts.c_ptr(), keep_names.c_ptr(), new_p,
                                         q->get_weight(), q->get_qid(), q->get_skid());
            }
        }

        void default_apply(bool forall, expr * p, quantifier * q, expr_ref & result) {
            quantifier_ref new_q(m);
            new_q = m.update_quantifier(q, forall, p);
            elim_unused_vars(m, new_q, result);
        }

        void apply(bool forall, expr * p, unsigned depth, quantifier * q, expr_ref & result) {
            checkpoint();
            if (depth > m_max_depth || m_curr_steps > m_max_steps) {
                default_apply(forall, p, q, result);
            }
            else {
                m_curr_steps++;
                expr * c;
                if (m.is_not(p, c)) {
                    apply(!forall, c, depth+1, q, result);
                    result = m.mk_not(result);
                }
                else if (m.is_and(p) && forall) {
                    easy_distribute_apply(forall, to_app(p), depth, q, result);
                }
                else if (m.is_or(p) && !forall) {
                    easy_distribute_apply(forall, to_app(p), depth, q, result);
                }
                else if (m.is_bool(p) && (m.is_ite(p) || m.is_iff(p) || m.is_and(p) || m.is_or(p) || (m.is_eq(p) && m.is_bool(to_app(p)->get_arg(0))))) {
                    distribute_apply(forall, to_app(p), depth, q, result);
                }
                else {
                    default_apply(forall, p, q, result);
                }
            }
        }

        bool reduce_quantifier(quantifier * old_q, 
                               expr * new_body, 
                               expr * const * new_patterns, 
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {
            m_curr_steps = 0;
            apply(old_q->is_forall(), new_body, 0, old_q, result);
            TRACE("miniscope", tout << mk_pp(old_q, m) << "\nnew_body:\n" << mk_pp(new_body, m) << "\n----->\n" << mk_pp(result, m) << "\n";);
            return true;
        }
    };

    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;
        
        rw(ast_manager & m, bool proofs_enabled, params_ref const & p):
            rewriter_tpl<rw_cfg>(m, proofs_enabled, m_cfg),
            m_cfg(m, p) {
        }
    };

    rw * m_rw;

    void apply(assertion_stream & g) {
        SASSERT(g.is_well_sorted());
        ast_manager & m = g.m();
        bool produce_proofs = g.proofs_enabled();
        rw r(m, produce_proofs, m_params);
        #pragma omp critical (tactic_cancel)
        {
            m_rw = &r;
        }
        stream_report report("miniscope", g);
        
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
                new_pr     = m.mk_modus_ponens(pr, new_pr);
            }
            g.update(idx, new_curr, new_pr, g.dep(idx));
        }
        g.inc_depth();
        TRACE("miniscope", g.display(tout););
        SASSERT(g.is_well_sorted());
        #pragma omp critical (tactic_cancel)
        {
            m_rw = 0;
        }
    }

    params_ref m_params;

public:
    miniscope_tactic(params_ref const & p):m_rw(0), m_params(p) {}

    virtual tactic * translate(ast_manager & m) {
        return alloc(miniscope_tactic, m_params);
    }

    virtual void updt_params(params_ref const & p) {
	m_params = p;
    }

    virtual void collect_param_descrs(param_descrs & r) { 
	miniscope_params::collect_param_descrs(r);
    }
    
    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        mc = 0; pc = 0; core = 0; result.reset();
        goal2stream s(*(g.get()));
        apply(s);
        result.push_back(g.get());
    }

    virtual void operator()(assertion_stack & s) {
        assertion_stack2stream strm(s);
        apply(strm);
    }
                            
    virtual void set_cancel(bool f) {
        if (m_rw) {
            m_rw->set_cancel(f);
            m_rw->cfg().set_cancel(f);
        }
    }

    virtual void cleanup() {}
};

tactic * mk_miniscope_tactic(ast_manager & m, params_ref const & p) {
    return alloc(miniscope_tactic, p);
}
