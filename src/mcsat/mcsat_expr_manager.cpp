/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_expr_manager.cpp

Abstract:

    Thread safe version of the ast_manager.
    It also supports push/pop.
    An expression created at level n is only deleted
    when level n is backtracked. 
    
    MCSat plugins can only create new expressions using
    the expr_manager. 

Author:

    Leonardo de Moura (leonardo) 2012-12-19

Revision History:

*/
#include"mcsat_expr_manager.h"
#include"mcsat_exception.h"
#include"ast_smt2_pp.h"

namespace mcsat {

    void expr_manager::push() {
        // Remark:
        // We do not need synchronization because when the
        // kernel performs a push, none of the plugins in the
        // kernel are running when push() is invoked.
        m_scopes.push_back(m_new_exprs.size());
    }

    void expr_manager::pop(unsigned num_scopes) {
        // Remark:
        // We do not need synchronization for reading m_scopes
        // and checking the size of m_new_exprs.size() because
        // none of the plugins in the kernel are running
        // when pop() is invoked.
        SASSERT(num_scopes <= m_scopes.size());
        unsigned new_lvl    = m_scopes.size() - num_scopes;
        unsigned old_sz     = m_scopes[new_lvl];
        SASSERT(old_sz <= m_new_exprs.size());
        if (old_sz < m_new_exprs.size()) {
            // we need synchronization here, because
            // a different kernel may be trying to access
            // the ast_manager in m_new_exprs
            #pragma omp critical (mcsat_expr_manager)
            {
                m_new_exprs.shrink(old_sz);
            }
        }
        m_scopes.shrink(new_lvl);
    }

    expr_manager::expr_manager(ast_manager & m):
        m_manager(m),
        m_new_exprs(m),
        m_curr_functor(0) {
    }

    expr_manager::~expr_manager() {
        if (!m_new_exprs.empty()) {
            #pragma omp critical (mcsat_expr_manager)
            {
                // We need synchronization because a different 
                // kernel may be trying to access the same ast_manager.
                m_new_exprs.reset();
            }
        }
    }

    family_id expr_manager::get_basic_family_id() const {
        return m().get_basic_family_id();
    }

    family_id expr_manager::get_family_id(symbol const & s) const {
        family_id fid;
        #pragma omp critical (mcsat_expr_manager)
        {
            fid = m().get_family_id(s);
        }
        return fid;
    }

    family_id expr_manager::get_family_id(char const * s) const {
        return get_family_id(symbol(s));
    }

    void expr_manager::set_cancel(bool f) {
        m().set_cancel(f);
        #pragma omp critical (mcsat_expr_manager_set_cancel)
        {
            if (m_curr_functor)
                m_curr_functor->set_cancel(f);
        }
    }
    
    void expr_manager::inc_ref(expr * n) {
        #pragma omp critical (mcsat_expr_manager)
        {
            m().inc_ref(n);
        }
    }
    
    void expr_manager::dec_ref(expr * n) {
        #pragma omp critical (mcsat_expr_manager)
        {
            m().dec_ref(n);
        }
    }

    void expr_manager::inc_ref(unsigned sz, expr * const * ns) {
        #pragma omp critical (mcsat_expr_manager)
        {
            for (unsigned i = 0; i < sz; i++)
                m().inc_ref(ns[i]);
        }
    }
    
    void expr_manager::dec_ref(unsigned sz, expr * const * ns) {
        #pragma omp critical (mcsat_expr_manager)
        {
            for (unsigned i = 0; i < sz; i++)
                m().dec_ref(ns[i]);
        }
    }

#define MK_BEGIN_CORE()                         \
    std::string msg;                            \
    bool caught_exception = false;              \
    unsigned error_code = 0;

#define MK_BEGIN()                              \
    app * r;                                    \
    MK_BEGIN_CORE();

#define MK_BODY(CODE)                           \
    try {                                       \
        CODE                                    \
    }                                           \
    catch (z3_error & err) {                    \
        error_code = err.error_code();          \
    }                                           \
    catch (z3_exception & ex) {                 \
        msg = ex.msg();                         \
        caught_exception = true;                \
    }

#define MK_END_CORE()                           \
    if (error_code != 0)                        \
        throw z3_error(error_code);             \
    if (caught_exception)                       \
        throw exception(msg.c_str());

#define MK_END()                                \
    MK_END_CORE();                              \
    m_new_exprs.push_back(r);                   \
    return r;

    app * expr_manager::mk_app(func_decl * decl, unsigned num_args, expr * const * args) {
        MK_BEGIN();
        #pragma omp critical (mcsat_expr_manager)
        {
            MK_BODY(r = m().mk_app(decl, num_args, args););
        }
        MK_END();
    }

    app * expr_manager::mk_app(func_decl * decl, expr * const * args) {
        return mk_app(decl, decl->get_arity(), args);
    }
    
    app * expr_manager::mk_app(func_decl * decl, expr * arg) {
        return mk_app(decl, 1, &arg);
    }

    app * expr_manager::mk_app(func_decl * decl, expr * arg1, expr * arg2) {
        expr * args[] = { arg1, arg2 };
        return mk_app(decl, 2, args);
    }

    app * expr_manager::mk_app(func_decl * decl, expr * arg1, expr * arg2, expr * arg3) {
        expr * args[] = { arg1, arg2, arg3 };
        return mk_app(decl, 3, args);
    }
    
    app * expr_manager::mk_const(func_decl * decl) {
        return mk_app(decl, 0, static_cast<expr * const *>(0));
    }

    app * expr_manager::mk_app(family_id fid, decl_kind k, unsigned num_parameters, parameter const * parameters, unsigned num_args, expr * const * args, sort * range) {
        MK_BEGIN();
        #pragma omp critical (mcsat_expr_manager)
        {
            MK_BODY(r = m().mk_app(fid, k, num_parameters, parameters, num_args, args, range););
        }
        MK_END();
    }

    app * expr_manager::mk_app(family_id fid, decl_kind k, unsigned num_args, expr * const * args) {
        return mk_app(fid, k, 0, 0, num_args, args);
    }

    app * expr_manager::mk_app(family_id fid, decl_kind k, expr * arg) {
        return mk_app(fid, k, 1, &arg);
    }

    app * expr_manager::mk_app(family_id fid, decl_kind k, expr * arg1, expr * arg2) {
        expr * args[] = { arg1, arg2 };
        return mk_app(fid, k, 2, args);
    }

    app * expr_manager::mk_app(family_id fid, decl_kind k, expr * arg1, expr * arg2, expr * arg3) {
        expr * args[] = { arg1, arg2, arg3 };
        return mk_app(fid, k, 3, args);
    }

    app * expr_manager::mk_const(family_id fid, decl_kind k) {
        return mk_app(fid, k, 0, static_cast<expr * const *>(0));
    }

    var * expr_manager::mk_var(unsigned idx, sort * s) {
        var * r;                                    
        MK_BEGIN_CORE();
        #pragma omp critical (mcsat_expr_manager)
        {
            MK_BODY(r = m().mk_var(idx, s););
        }
        MK_END_CORE();
        m_new_exprs.push_back(r);
        return r;
    }

    void expr_manager::functor::set_cancel(bool f) {
    }

    struct expr_manager::set_functor {
        expr_manager & m_owner;
        set_functor(expr_manager & m, expr_manager::functor & f):m_owner(m) {
            SASSERT(m_owner.m_curr_functor == 0);
            #pragma omp critical (mcsat_expr_manager_set_cancel)
            {
                m_owner.m_curr_functor = &f;
            }
        }
        ~set_functor() {
            #pragma omp critical (mcsat_expr_manager_set_cancel)
            {
                m_owner.m_curr_functor = 0;
            }
        }
    };
     
    void expr_manager::apply(functor & f) {
        MK_BEGIN_CORE();
        #pragma omp critical (mcsat_expr_manager)
        {
            MK_BODY({
                    set_functor setter(*this, f);
                    store_expr_functor p(m_new_exprs);
                    f(m(), p);
                });
        }
        MK_END_CORE();
    }

    void expr_manager::display(std::ostream & out, expr * t, params_ref const & params, unsigned indent, unsigned num_vars, char const * var_prefix) const {
        MK_BEGIN_CORE();
        #pragma omp critical (mcsat_expr_manager)
        {
            MK_BODY({
                    smt2_pp_environment_dbg env(m());
                    ast_smt2_pp(out, t, env, params, indent, num_vars, var_prefix);
                });
        }
        MK_END_CORE();
    }

    mk_pp::mk_pp(expr * e, expr_manager & m, unsigned indent, unsigned num_vars, char const * var_prefix):
        m_expr(e),
        m_manager(m),
        m_params(params_ref::get_empty()),
        m_indent(indent),
        m_num_vars(num_vars),
        m_var_prefix(var_prefix) {
    }
    
    mk_pp::mk_pp(expr * e, expr_manager & m, params_ref const & p, unsigned indent, unsigned num_vars, char const * var_prefix):
        m_expr(e),
        m_manager(m),
        m_params(p),
        m_indent(indent),
        m_num_vars(num_vars),
        m_var_prefix(var_prefix) {
    }
    
    std::ostream & operator<<(std::ostream & out, mk_pp const & p) {
        p.m_manager.display(out, p.m_expr, p.m_params, p.m_indent, p.m_num_vars, p.m_var_prefix);
        return out;
    }

};
