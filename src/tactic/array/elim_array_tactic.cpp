/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    elim_array_tactic.cpp

Abstract:
    
    Eliminate array terms using unintepreted functions
    
Author:

    Leonardo de Moura (leonardo) 2013-02-07

Revision History:

--*/
#include"tactical.h"
#include"assertion_stream.h"
#include"ast_util.h"
#include"array_decl_plugin.h"
#include"extension_model_converter.h"
#include"rewriter_def.h"

class elim_array_tactic : public tactic {

    struct rw_cfg : public default_rewriter_cfg {
        ast_manager & m;
        array_util    m_util;

        rw_cfg(ast_manager & _m):m(_m), m_util(m) {
        }

        void throw_not_supported() {
            throw tactic_exception("failed to reduce array theory to UF");
        }

        br_status reduce_eq(expr * lhs, expr * rhs, expr_ref & result) {
            sort * s = get_sort(lhs);
            if (!m_util.is_array(s))
                return BR_FAILED;
            // convert into Forall i: select(lhs, i) = select(rhs, i)
            sort_ref_buffer sorts(m);
            sbuffer<symbol> names;
            unsigned arity = get_array_arity(s);
            expr_ref_buffer lhs_args(m);
            expr_ref_buffer rhs_args(m);
            lhs_args.push_back(lhs);
            rhs_args.push_back(rhs);
            for (unsigned i = 0; i < arity; i++) {
                unsigned vidx = arity - i - 1;
                sort * vsort  = get_array_domain(s, i);
                var * v       = m.mk_var(vidx, vsort);
                lhs_args.push_back(v);
                rhs_args.push_back(v);
                sorts.push_back(vsort);
                names.push_back(mk_fresh_symbol("i"));
            }
            result = m.mk_forall(sorts.size(), sorts.c_ptr(), names.c_ptr(), m.mk_eq(m_util.mk_select(lhs_args.size(), lhs_args.c_ptr()),
                                                                                     m_util.mk_select(rhs_args.size(), rhs_args.c_ptr())));
            return BR_REWRITE3;
        }

        br_status reduce_distinct(unsigned num, expr * const * args, expr_ref & result) {
            if (num == 0 || !m_util.is_array(get_sort(args[0])))
                return BR_FAILED;
            result = expand_distinct(m, num, args);
            return BR_REWRITE3;
        }

        br_status reduce_select(unsigned num, expr * const * args, expr_ref & result) {
            if (!is_app(args[0]))
                throw_not_supported();
            if (num == 0)
                return BR_FAILED;
            app * array = to_app(args[0]);
            if (m.is_ite(array)) {
                // lift ite
                ptr_buffer<expr> t_args;
                ptr_buffer<expr> e_args;
                t_args.push_back(array->get_arg(1));
                e_args.push_back(array->get_arg(2));
                for (unsigned i = 1; i < num; i++) {
                    t_args.push_back(args[i]);
                    e_args.push_back(args[i]);
                }
                result = m.mk_ite(array->get_arg(0), m_util.mk_select(t_args.size(), t_args.c_ptr()), m_util.mk_select(e_args.size(), e_args.c_ptr()));
                return BR_REWRITE2;
            }
            else if (m_util.is_store(array)) {
                SASSERT(array->get_num_args() == num + 1);
                expr * array_0 = array->get_arg(0);
                expr * val     = array->get_arg(num);
                expr_ref_buffer  eqs(m);
                ptr_buffer<expr> s_args;
                s_args.push_back(array_0);
                for (unsigned i = 1; i < num; i++) {
                    s_args.push_back(args[i]);
                    eqs.push_back(m.mk_eq(array->get_arg(i), args[i]));
                }
                result = m.mk_ite(mk_and(m, eqs.size(), eqs.c_ptr()), val, m_util.mk_select(s_args.size(), s_args.c_ptr()));
                return BR_REWRITE2;
            }
            else if (m_util.is_map(array)) {
                func_decl * f = m_util.get_map_func_decl(array);
                expr_ref_buffer f_args(m);
                ptr_buffer<expr> s_args;
                for (unsigned i = 0; i < array->get_num_args(); i++) {
                    s_args.reset();
                    s_args.push_back(array->get_arg(i));
                    for (unsigned j = 1; j < num; j++) {
                        s_args.push_back(args[j]);
                    }
                    f_args.push_back(m_util.mk_select(s_args.size(), s_args.c_ptr()));
                }
                result = m.mk_app(f, f_args.size(), f_args.c_ptr());
                return BR_REWRITE2;
            }
            else if (m_util.is_const(array)) {
                result = array->get_arg(0);
                return BR_DONE;
            }
            else if (m_util.is_as_array(array)) {
                func_decl * f = m_util.get_as_array_func_decl(array);
                result = m.mk_app(f, num-1, args+1);
                return BR_DONE;
            }
            else if (m_util.is_select(array)) {
                // TODO
            }
            else if (is_uninterp_const(array)) {
                // TODO
            }
            else {
                throw_not_supported();
            }
            return BR_FAILED;
        }
       
        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            if (m.is_eq(f)) {
                SASSERT(num == 2);
                return reduce_eq(args[0], args[1], result);
            }
            else if (m.is_distinct(f)) {
                return reduce_distinct(num, args, result);
            }
            else if (m_util.is_select(f)) {
                return reduce_select(num, args, result); 
            } 
            else if (f->get_family_id() == m_util.get_family_id()) {
                switch (f->get_decl_kind()) {
                case OP_SELECT: UNREACHABLE();
                case OP_STORE:
                case OP_CONST_ARRAY:
                case OP_ARRAY_MAP:
                case OP_AS_ARRAY:
                    // do nothing at this point
                    return BR_FAILED;
                default:
                    throw_not_supported();
                    return BR_FAILED;
                }
            }
            else {
                // args should not be array terms
                for (unsigned i = 0; i < num; i++) {
                    if (m_util.is_array(get_sort(args[i])))
                        throw_not_supported();
                }
                return BR_FAILED;
            }
        }

        bool reduce_quantifier(quantifier * old_q, 
                               expr * new_body, 
                               expr * const * new_patterns, 
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {
            // quantification over arrays is not allowed
            for (unsigned i = 0; i < old_q->get_num_decls(); i++) {
                if (m_util.is_array(old_q->get_decl_sort(i)))
                    throw_not_supported();
            }
            return false;
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
        elim_array_tactic & m;
        set_rw(elim_array_tactic & _m, rw & r):m(_m) {
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
        stream_report report("elim_array", g);
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
        TRACE("elim_array", g.display(tout););
        SASSERT(g.is_well_sorted());
    }

public:    
    elim_array_tactic():m_rw(0) {}

    virtual tactic * translate(ast_manager & m) {
        return alloc(elim_array_tactic);
    }

    virtual void updt_params(params_ref const & p) {}
    virtual void collect_param_descrs(param_descrs & r) {}
    
    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        TRACE("elim_array_detail", tout << "input goal\n"; g->display(tout););
        mc = 0; pc = 0; core = 0; result.reset();
        goal_and_emc2stream s(*(g.get()));
        apply(s);
        if (g->models_enabled())
            mc = s.mc();
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
        }
    }

    virtual void cleanup() {}
};

tactic * mk_elim_array_tactic(ast_manager & m, params_ref const & p) {
    return alloc(elim_array_tactic);
}
