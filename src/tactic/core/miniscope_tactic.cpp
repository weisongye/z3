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
#include"nnf_tactic.h"
#include"simplify_tactic.h"
#include"cooperate.h"
#include"has_free_vars.h"
#include"miniscope_params.hpp"

class miniscope_tactic : public tactic {

    struct rw_cfg : public default_rewriter_cfg {
        ast_manager & m;

        unsigned m_max_depth;
        unsigned m_max_steps;
        unsigned m_curr_steps;
        bool     m_preserve_patterns;
        bool     m_select_least;
        volatile bool m_cancel;   

        rw_cfg(ast_manager & _m, params_ref const & _p):m(_m) {
            miniscope_params p(_p);
            m_max_depth         = p.max_depth();
            m_max_steps         = p.max_steps();
            m_preserve_patterns = p.preserve_patterns();
            m_select_least      = p.select_least();
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

        // Force vidx to be the variable 0
        void swap_var(unsigned vidx, app * p, quantifier * q, app_ref & new_p) {
            if (vidx == 0) {
                new_p = p;
            }
            else {
                unsigned num_vars = q->get_num_decls();
                expr_ref new_v0(m), new_vi(m);
                new_v0 = m.mk_var(0, q->get_decl_sort(num_vars - vidx - 1));
                new_vi = m.mk_var(vidx, q->get_decl_sort(num_vars - 1));
                expr_ref_buffer subst(m);
                subst.resize(num_vars);
                subst.set(num_vars - 1,        new_vi);
                subst.set(num_vars - vidx - 1, new_v0);
                var_subst s(m);
                expr_ref aux(m);
                s(p, subst.size(), subst.c_ptr(), aux);
                TRACE("miniscope_bug", tout << "swap_var\n" << mk_pp(p, m) << "\n---->\n" << mk_pp(aux, m) << "\n";);
                new_p = to_app(aux);
            }
        }
        
        bool has_patterns(quantifier * q) {
            return q->get_num_patterns() > 0 || q->get_num_no_patterns() > 0;
        }
        
        // Select the first variable that does not occur in all children of p.
        // Return UINT_MAX if all variables occur in all children of p.
        unsigned select_first(app * p, quantifier * q) {
            unsigned      num_vars = q->get_num_decls();
            for (unsigned v = 0; v < num_vars; v++) {
                for (unsigned i = 0; i < p->get_num_args(); i++) {
                    expr * c = p->get_arg(i);
                    if (!has_free_vars(c, v, v))
                        return v;
                }
            }
            return UINT_MAX;
        }

        // Select the variable that occurs in the least number of children of p.
        // Return UINT_MAX if all variables occur in all children of p.
        unsigned select_least(app * p, quantifier * q) {
            unsigned r    = UINT_MAX;
            unsigned best = p->get_num_args();
            unsigned num_vars = q->get_num_decls();
            for (unsigned v = 0; v < num_vars; v++) {
                unsigned counter = 0;
                for (unsigned i = 0; i < p->get_num_args(); i++) {
                    expr * c = p->get_arg(i);
                    if (has_free_vars(c, v, v))
                        counter++;
                }
                if (counter < best) {
                    r    = v;
                    best = counter;
                }
            }
            return r;
        }

        void distribute_apply_iter(bool forall, app * p, unsigned depth, quantifier * q, expr_ref & result) {
            TRACE("miniscope_detail", tout << "distribute_apply_iter [" << depth << "]\n" << mk_pp(p, m) << "\nq:\n" << mk_pp(q, m) << "\n";);
            checkpoint();
            if (depth > m_max_depth || m_curr_steps > m_max_steps) {
                default_apply(forall, p, q, result);
            }
            else {
                // find first variable that does not occurr in all children of p
                unsigned v = m_select_least ? select_least(p, q) : select_first(p, q);
                if (v == UINT_MAX) {
                    // all variables occur in all children
                    default_apply(forall, p, q, result);
                }
                else {
                    unsigned      num_vars = q->get_num_decls();
                    sbuffer<unsigned> v_children_idxs;  // positition of the children that contain v.
                    sbuffer<unsigned> nv_children_idxs; // positition of the children that do not contain v.
                    for (unsigned i = 0; i < p->get_num_args(); i++) {
                        expr * c = p->get_arg(i);
                        if (has_free_vars(c, v, v))
                            v_children_idxs.push_back(i);
                        else
                            nv_children_idxs.push_back(i);
                    }
                    SASSERT(!nv_children_idxs.empty());
                    // at least one children does not contain v.
                    app_ref new_p(m);
                    // rename v to 0, and store new formula in new_p
                    swap_var(v, p, q, new_p);
                    // split quantifier variables
                    symbol           v_name;
                    sbuffer<symbol>  nv_names;
                    sort *           v_sort;
                    ptr_buffer<sort> nv_sorts;
                    v_name = q->get_decl_name(num_vars - v - 1);
                    v_sort = q->get_decl_sort(num_vars - v - 1);
                    for (unsigned i = 0; i < num_vars; i++) {
                        if (i != num_vars - v - 1) {
                            nv_names.push_back(q->get_decl_name(i));
                            nv_sorts.push_back(q->get_decl_sort(i));
                        }
                    }
                    // split children
                    expr_ref_buffer v_children(m);
                    expr_ref_buffer nv_children(m);
                    expr_ref new_c(m);
                    inv_var_shifter s(m);
                    unsigned num_nv_children = nv_children_idxs.size();
                    for (unsigned i = 0; i < num_nv_children; i++) {
                        s(new_p->get_arg(nv_children_idxs[i]), 1, new_c);
                        nv_children.push_back(new_c);
                    }
                    unsigned num_v_children = v_children_idxs.size();
                    for (unsigned i = 0; i < num_v_children; i++)
                        v_children.push_back(new_p->get_arg(v_children_idxs[i]));
                    if (num_v_children > 1) {
                        expr_ref p0(m);
                        p0 = m.mk_app(p->get_decl(), num_v_children, v_children.c_ptr());
                        quantifier_ref q0(m);
                        q0 = m.mk_quantifier(forall, 1, &v_sort, &v_name, p0,
                                             q->get_weight(), q->get_qid(), q->get_skid());
                        nv_children.push_back(q0);
                    }
                    else if (num_v_children == 1) {
                        quantifier_ref q0(m);
                        q0 = m.mk_quantifier(forall, 1, &v_sort, &v_name, v_children[0],
                                             q->get_weight(), q->get_qid(), q->get_skid());
                        expr_ref p0(m);
                        apply(forall, v_children[0], depth+1, q0, p0);
                        nv_children.push_back(p0);
                    }
                    SASSERT(nv_children.size() > 1);
                    new_p = m.mk_app(p->get_decl(), nv_children.size(), nv_children.c_ptr());
                    if (nv_names.empty()) {
                        result = new_p;
                    }
                    else {
                        quantifier_ref new_q(m);
                        new_q = m.mk_quantifier(forall, nv_sorts.size(), nv_sorts.c_ptr(), nv_names.c_ptr(), new_p,
                                                q->get_weight(), q->get_qid(), q->get_skid());
                        distribute_apply_iter(forall, new_p, depth+1, new_q, result);
                    }
                }
            }
        }

        void distribute_apply(bool forall, app * p, unsigned depth, quantifier * q, expr_ref & result) {
            if (!m_preserve_patterns || !has_patterns(q)) {
                distribute_apply_iter(forall, p, depth, q, result);
            }
            else {
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
                if (std::find(keep.begin(), keep.end(), true) == keep.end()) {
                    // the sets of used variables are disjoint... this is an easy case
                    easy_distribute_apply(forall, p, depth, q, result);
                }
                else {
                    default_apply(forall, p, q, result);
                }
            }
        }

        void default_apply(bool forall, expr * p, quantifier * q, expr_ref & result) {
            quantifier_ref new_q(m);
            new_q = m.update_quantifier(q, forall, p);
            elim_unused_vars(m, new_q, result);
        }

        void apply_quantifier(bool forall, quantifier * p, unsigned depth, quantifier * q, expr_ref & result) {
            if (m_preserve_patterns && (has_patterns(p) || has_patterns(q))) {
                default_apply(forall, p, q, result);
            }
            else {
                sbuffer<symbol>   names;
                ptr_buffer<sort>  sorts;
                names.append(q->get_num_decls(), q->get_decl_names());
                names.append(p->get_num_decls(), p->get_decl_names());
                sorts.append(q->get_num_decls(), q->get_decl_sorts());
                sorts.append(p->get_num_decls(), p->get_decl_sorts());
                quantifier_ref new_q(m);
                new_q = m.mk_quantifier(forall, sorts.size(), sorts.c_ptr(), names.c_ptr(), p->get_expr(),
                                        q->get_weight(), q->get_qid(), q->get_skid());
                TRACE("miniscope_bug", tout << mk_pp(p, m) << "\n" << mk_pp(q, m) << "\n----->\n" << mk_pp(new_q, m) << "\n";);
                apply(forall, new_q->get_expr(), depth+1, new_q, result);
            }
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
                else if (m.is_and(p) || m.is_or(p)) {
                    distribute_apply(forall, to_app(p), depth, q, result);
                }
                else if (is_quantifier(p) && forall == to_quantifier(p)->is_forall()) {
                    apply_quantifier(forall, to_quantifier(p), depth, q, result);
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

    rw *  m_rw;

    struct set_rw {
        miniscope_tactic & m;
        set_rw(miniscope_tactic & _m, rw & r):m(_m) {
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
        stream_report report("miniscope", g);
        bool produce_proofs = g.proofs_enabled();

        rw r(m, produce_proofs, m_params);
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
        TRACE("miniscope", g.display(tout););
        SASSERT(g.is_well_sorted());
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
        TRACE("miniscope_detail", tout << "input goal\n"; g->display(tout););
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
        if (m_rw) {
            m_rw->set_cancel(f);
            m_rw->cfg().set_cancel(f);
        }
    }

    virtual void cleanup() {}
};

tactic * mk_miniscope_tactic_core(ast_manager & m, params_ref const & p) {
    return alloc(miniscope_tactic, p);
}

tactic * mk_miniscope_tactic(ast_manager & m, params_ref const & p) {
    params_ref np;
    np.set_bool("skolemize", false);
    np.set_bool("ignore_nested", true);
    np.set_sym("mode", symbol("quantifiers"));
    return and_then(using_params(mk_nnf_tactic(m), np),
                    mk_simplify_tactic(m),
                    mk_miniscope_tactic_core(m, p));
}

