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
#include"var_subst.h"
#include"ast_pp.h"

class elim_array_tactic : public tactic {

    struct rw_cfg : public default_rewriter_cfg {
        ast_manager &            m;
        array_util               m_util;
        obj_map<func_decl, app*> m_definitions;
        obj_map<app, app*>       m_names; // names for composite array terms that occur as arguments of uninterpreted functions
        ast_ref_vector           m_asts;
        assertion_stream *       m_stream;
        var_shifter              m_shift;
        var_subst                m_subst;
        
        bool                     m_fail_if_not_supported;

        rw_cfg(ast_manager & _m):
            m(_m), 
            m_util(m),
            m_asts(m),
            m_stream(0),
            m_shift(m),
            m_subst(m, false /* does not use standard order */) {

            m_fail_if_not_supported = false;
        }

        void throw_unexpected() {
            throw tactic_exception("failed to reduce array theory to UF, unexpected input");
        }

        void throw_not_supported() {
            if (m_fail_if_not_supported)
                throw tactic_exception("failed to reduce array theory to UF");
        }

        app * add_def(func_decl * f) {
            SASSERT(m_stream);
            if (m_stream->is_frozen(f)) {
                // this can only happen if the tactic is applied to an
                // assertion stream where a push was performed but the
                // tactic was not applied.
                throw_unexpected();
            }
            app * r;
            if (m_definitions.find(f, r)) {
                return r;
            }
            else {
                ptr_buffer<sort> d;
                sbuffer<unsigned> nargs;
                unsigned arity = f->get_arity();
                for (unsigned i = 0; i < arity; i++)
                    d.push_back(f->get_domain(i));
                sort * r = f->get_range();
                SASSERT(m_util.is_array(r));
                while (m_util.is_array(r)) {
                    unsigned num = get_array_arity(r);
                    nargs.push_back(num);
                    for (unsigned i = 0; i < num; i++)
                        d.push_back(get_array_domain(r, i));
                    r = get_array_range(r);
                }
                SASSERT(!nargs.empty());
                std::reverse(nargs.begin(), nargs.end());
                if (arity == 0)
                    nargs.pop_back();
                app_ref a(m);
                a = m_util.mk_as_array(m.mk_fresh_func_decl(f->get_name(), symbol::null, d.size(), d.c_ptr(), r));
                for (unsigned i = 0; i < nargs.size(); i++) {
                    a = m_util.mk_curry(nargs[i], a);
                }
                // TODO: to support proofs we have to create a def_intro object
                if (arity > 0) {
                    expr_ref_buffer  s_args(m);
                    expr_ref_buffer  f_args(m);
                    s_args.push_back(a);
                    for (unsigned i = 0; i < arity; i++) {
                        var * x = m.mk_var(i, f->get_domain(i));
                        s_args.push_back(x);
                        f_args.push_back(x);
                    }
                    sbuffer<symbol>  names;
                    ptr_buffer<sort> sorts;
                    unsigned i = arity;
                    while (i > 0) {
                        --i;
                        names.push_back(mk_fresh_symbol("x"));
                        sorts.push_back(f->get_domain(i));
                    }
                    a = m_util.mk_select(s_args.size(), s_args.c_ptr());
                    quantifier_ref q(m);
                    q = m.mk_forall(sorts.size(), sorts.c_ptr(), names.c_ptr(), m.mk_eq(m.mk_app(f, f_args.size(), f_args.c_ptr()), a));
                    m_stream->add_definition(f, q, 0, 0);
                }
                else {
                    m_stream->add_definition(m.mk_const(f), a, 0, 0);
                }
                m_asts.push_back(f);
                m_asts.push_back(a);
                m_definitions.insert(f, a);
                return a;
            }
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
            expr_ref new_lhs(m);
            expr_ref new_rhs(m);
            m_shift(lhs, arity, new_lhs);
            m_shift(rhs, arity, new_rhs);
            lhs_args.push_back(new_lhs);
            rhs_args.push_back(new_rhs);
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

        expr * uncurry(unsigned num, expr * arg) {
            while (num > 0 && m_util.is_curry(arg)) {
                arg = to_app(arg)->get_arg(0);
                num--;
            }
            for (unsigned i = 0; i < num; i++)
                arg = m_util.mk_uncurry(arg);
            return arg;
        }

        br_status reduce_select(unsigned num, expr * const * args, expr_ref & result) {
            if (!is_app(args[0])) {
                throw_not_supported();
                return BR_FAILED;
            }
            if (num == 0)
                return BR_FAILED;
            app * array = to_app(args[0]);
            unsigned num_uncurry = 0;
            while (m_util.is_uncurry(array)) {
                num_uncurry++;
                if (!is_app(array->get_arg(0))) {
                    throw_not_supported();
                    return BR_FAILED;
                }
                array = to_app(array->get_arg(0));
            }
            if (m.is_ite(array)) {
                // lift ite
                expr_ref_buffer t_args(m);
                expr_ref_buffer e_args(m);
                t_args.push_back(uncurry(num_uncurry, array->get_arg(1)));
                e_args.push_back(uncurry(num_uncurry, array->get_arg(2)));
                for (unsigned i = 1; i < num; i++) {
                    t_args.push_back(args[i]);
                    e_args.push_back(args[i]);
                }
                result = m.mk_ite(array->get_arg(0), m_util.mk_select(t_args.size(), t_args.c_ptr()), m_util.mk_select(e_args.size(), e_args.c_ptr()));
                return BR_REWRITE2;
            }
            else if (m_util.is_store(array)) {
                SASSERT(num_uncurry != 0 || array->get_num_args() == num + 1);
                expr * array_0 = array->get_arg(0);
                expr * val     = array->get_arg(num);
                expr_ref_buffer  eqs(m);
                expr_ref_buffer  s_args(m);
                s_args.push_back(uncurry(num_uncurry, array_0));
                for (unsigned i = 1; i < array->get_num_args() - 1; i++) {
                    s_args.push_back(args[i]);
                    eqs.push_back(m.mk_eq(array->get_arg(i), args[i]));
                }
                if (num_uncurry == 0) {
                    result = m.mk_ite(mk_and(m, eqs.size(), eqs.c_ptr()), val, m_util.mk_select(s_args.size(), s_args.c_ptr()));
                }
                else {
                    SASSERT(m_util.is_array(val));
                    expr_ref_buffer s_v_args(m);
                    s_v_args.push_back(uncurry(num_uncurry - 1, val));
                    for (unsigned i = 1 + array->get_num_args(); i < num; i++) {
                        s_v_args.push_back(args[i]);
                    }
                    result = m.mk_ite(mk_and(m, eqs.size(), eqs.c_ptr()), 
                                      m_util.mk_select(s_v_args.size(), s_v_args.c_ptr()),
                                      m_util.mk_select(s_args.size(), s_args.c_ptr()));
                }
                return BR_REWRITE2;
            }
            else if (m_util.is_map(array)) {
                func_decl * f = m_util.get_map_func_decl(array);
                expr_ref_buffer f_args(m);
                expr_ref_buffer s_args(m);
                for (unsigned i = 0; i < array->get_num_args(); i++) {
                    s_args.reset();
                    s_args.push_back(uncurry(num_uncurry, array->get_arg(i)));
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
                if (num_uncurry > 0) {
                    // Here is an example:
                    //   f : Int -> (Array Bool Int)
                    // Then, as_array[f] is an array (Array Int (Array Bool Int))
                    // And, uncurry(as_array[f]) is (Array Int Bool Int)
                    // We rewrite
                    //     select(uncurry(as_array[f]), i, j)
                    // into
                    //     select(f(i), j)
                    expr_ref_buffer s_args(m);
                    s_args.push_back(uncurry(num_uncurry - 1, m.mk_app(f, f->get_arity(), args+1)));
                    for (unsigned i = f->get_arity() + 1; i < num; i++)
                        s_args.push_back(args[i]);
                    result = m_util.mk_select(s_args.size(), s_args.c_ptr());
                    return BR_REWRITE2;
                }
                else {
                    SASSERT(f->get_arity() == num-1);
                    expr_ref_buffer new_args(m);
                    if (reduce_array_args_core(num-1, args+1, new_args)) {
                        result = m.mk_app(f, new_args.size(), new_args.c_ptr());
                        return BR_REWRITE2;
                    }
                    else {
                        result = m.mk_app(f, num-1, args+1);
                        return BR_DONE;
                    }
                }
            }
            else if (m_util.is_select(array)) {
                num_uncurry++;
                expr_ref_buffer s_args(m);
                s_args.push_back(uncurry(num_uncurry, to_app(array)->get_arg(0)));
                for (unsigned i = 1; i < to_app(array)->get_num_args(); i++) {
                    s_args.push_back(to_app(array)->get_arg(i));
                }
                for (unsigned i = 1; i < num; i++) {
                    s_args.push_back(args[i]);
                }
                result = m_util.mk_select(s_args.size(), s_args.c_ptr());
                return BR_REWRITE1;
            }
            else if (m_util.is_curry(array)) {
                if (num_uncurry == 0)
                    return BR_FAILED;
                else {
                    expr_ref_buffer s_args(m);
                    s_args.push_back(uncurry(num_uncurry-1, array->get_arg(0)));
                    for (unsigned i = 0; i < num; i++)
                        s_args.push_back(args[i]);
                    result = m_util.mk_select(s_args.size(), s_args.c_ptr());
                    return BR_REWRITE1;
                }
            }
            else {
                throw_not_supported();
            }
            return BR_FAILED;
        }

        expr * mk_name_for(app * a) {
            SASSERT(m_util.is_array(a));
            app * r;
            if (m_names.find(a, r)) {
                return r;
            }
            else {
                sort * s = get_sort(a);
                app * r = m.mk_fresh_const("array", s);
                m_stream->add_filter(r->get_decl());
                m_stream->assert_expr(m.mk_eq(r, a));
                m_asts.push_back(r); 
                m_asts.push_back(a);
                m_names.insert(a, r);
                return r;
            }
        }

        bool reduce_array_args_core(unsigned num, expr * const * args, expr_ref_buffer & new_args) {
            bool reduced = false;
            for (unsigned i = 0; i < num; i++) {
                expr * arg = args[i];
                // In principle, we can relax the condition is_ground(arg).
                // To do that, we have to create a function instead of a constant.
                // For example, assume x is a variable and A and i are constants.
                // Then assume arg is the term.
                //    store(A, i, x)
                // Then, we could create a fresh function f that takes two arguments, and replace the store with
                //    (select (curry (_ as_array f)) x)
                // The first argument of f is used to pass the value of x, and the second is the index.
                // We also add the axiom
                //    forall x, j: f(x, j) = ite(i == j, x, select(A, j))
                // This can be done to eliminate store, map and const even when they contain variables (i.e., are not ground).
                // However, the resulting expression is still messy. 
                // Moreover, this kind of usage pattern is very uncommon. So, I will wait until anybody uses it.
                // In the meatime, I just keep the store/const/map.
                if (m_util.is_array(arg) && is_app(arg) && is_ground(arg) && to_app(arg)->get_family_id() == m_util.get_family_id()) {
                    switch (to_app(arg)->get_decl_kind()) {
                    case OP_STORE:
                    case OP_CONST_ARRAY:
                    case OP_ARRAY_MAP: {
                        new_args.push_back(mk_name_for(to_app(arg)));
                        reduced = true;
                        break;
                    }
                    default:
                        new_args.push_back(arg);
                        break;
                    }
                }
                else {
                    new_args.push_back(arg);
                }
            }
            return reduced;
        }

        br_status reduce_uninterp(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
            app * a = add_def(f);
            // TODO: to support proofs we have to create a proof object, that uses the proof that a and f are "equivalent"
            if (num == 0) {
                result = a;
                return BR_DONE;
            }
            else {
                expr_ref_buffer new_args(m);
                reduce_array_args_core(num, args, new_args);
                SASSERT(new_args.size() == num);
                m_subst(a, num, new_args.c_ptr(), result);
                return BR_REWRITE2;
            }
        }

        br_status reduce_array_args(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
            SASSERT(!m_fail_if_not_supported);
            // Create aliases for the array arguments
            expr_ref_buffer new_args(m);
            if (reduce_array_args_core(num, args, new_args)) {
                SASSERT(new_args.size() == num);
                result = m.mk_app(f, num, new_args.c_ptr());
                return BR_REWRITE2;
            }
            else {
                return BR_FAILED;
            }
        }
       
        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            if (m.is_eq(f)) {
                SASSERT(num == 2);
                return reduce_eq(args[0], args[1], result);
            }
            else if (m.is_ite(f)) {
                return BR_FAILED;
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
                case OP_CURRY:
                case OP_UNCURRY:
                    // do nothing at this point
                    return BR_FAILED;
                default:
                    throw_not_supported();
                    return BR_FAILED;
                }
            }
            else {
                // args should not be array terms
                bool has_array_arg = false;
                for (unsigned i = 0; i < num; i++) {
                    if (m_util.is_array(get_sort(args[i])))
                        has_array_arg = true;
                }
                if (has_array_arg && m_fail_if_not_supported) {
                    throw_not_supported();
                }
                if (m_util.is_array(f->get_range())) {
                    if (is_uninterp(f))
                        return reduce_uninterp(f, num, args, result);
                    else
                        throw_not_supported();
                }
                else if (has_array_arg) {
                    return reduce_array_args(f, num, args, result);
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
        fail_if_proof_generation("elim_array", produce_proofs); // TODO: add support for proofs, see comments above
        rw r(m, produce_proofs);
        set_rw s(*this, r);
        r.cfg().m_stream = &g;
        expr_ref   new_curr(m);
        proof_ref  new_pr(m);
        for (unsigned idx = g.qhead(); idx < g.size(); idx++) {
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
        goal_and_femc2stream s(*(g.get()));
        apply(s);
        if (g->models_enabled())
            mc = s.combined_mc();
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
