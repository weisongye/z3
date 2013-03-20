/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_expr_manager.h

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
#ifndef _EXPR_MANAGER_H_
#define _EXPR_MANAGER_H_

#include"ast.h"
#include"params.h"

namespace mcsat {

    /**
       \brief This is a thread safe version of ast_manager.
       It can concurrently accessed by many different threads.
       
       MCSat plugins should minimize the access to expr_manager, since
       it reduces the amount of parallelism in the system.
       We may have only one thread accessing the shared ast_manager.
    */
    class expr_manager {
    public:
        struct functor;
        struct set_functor;
        class store_expr_functor {
            friend class expr_manager;
            expr_ref_vector & m_to_save;
            store_expr_functor(expr_ref_vector & to_save):m_to_save(to_save) {}
        public:
            void operator()(expr * n) { m_to_save.push_back(n); }
        };
    private:
        friend struct set_functor;
        friend class kernel;
        ast_manager &   m_manager;
        expr_ref_vector m_new_exprs;
        unsigned_vector m_scopes;
        functor *       m_curr_functor;
        expr_manager(ast_manager & m);
        ~expr_manager();

        // The kernel uses reference counting when creating clauses.
        // When the kernel creates a clause, it bumps the reference
        // counter of the expressions representing the literals.
        // It needs to do that because:
        //   1) lemmas may remain alive even after the scope level 
        //      that created them is backtracked.
        //   2) pop/push cleanup idiom. We destroy the current scope level
        //      and recreate it. 
        void inc_ref(expr * n);
        void dec_ref(expr * n);
        void inc_ref(unsigned sz, expr * const * ns);
        void dec_ref(unsigned sz, expr * const * ns);
        //

        void push();
        void pop(unsigned num_scopes);
        ast_manager & m() const { return m_manager; }
    public:
        void set_cancel(bool f);

        family_id get_basic_family_id() const;
        family_id get_family_id(symbol const & s) const;
        family_id get_family_id(char const * s) const;

        app * mk_app(func_decl * decl, unsigned num_args, expr * const * args);
        app * mk_app(func_decl * decl, expr * const * args);
        app * mk_app(func_decl * decl, expr * arg);
        app * mk_app(func_decl * decl, expr * arg1, expr * arg2);
        app * mk_app(func_decl * decl, expr * arg1, expr * arg2, expr * arg3);
        app * mk_const(func_decl * decl);
        app * mk_app(family_id fid, decl_kind k, unsigned num_parameters = 0, parameter const * parameters = 0, unsigned num_args = 0, expr * const * args = 0, sort * range = 0);
        app * mk_app(family_id fid, decl_kind k, unsigned num_args, expr * const * args);
        app * mk_app(family_id fid, decl_kind k, expr * arg);
        app * mk_app(family_id fid, decl_kind k, expr * arg1, expr * arg2);
        app * mk_app(family_id fid, decl_kind k, expr * arg1, expr * arg2, expr * arg3);
        app * mk_const(family_id fid, decl_kind k);
        var * mk_var(unsigned idx, sort * s);
   
        /**
           \brief Functor for obtaining direct access to the the ast_manager.

           \sa apply(functor & f);
        */
        struct functor {
            virtual void operator()(ast_manager & m, store_expr_functor & to_save) = 0;
            virtual void set_cancel(bool f);
        };
        /**
           \brief Execute the given functor f(ast_manager & m, expr_ref_vector & to_protect).
           
           The functor will have direct access to the ast_manager.
           The references to the ast_manager and expr_saver should NOT be saved by the functor for later use. 
           That is, after functor::operator() returns.
           The functor should NOT invoke any method of this expr_manager.
           Any expression created by the functor should be stored in to_protect.
           This procedure will block any thread trying to access the expr_manager.
        */
        void apply(functor & f);
        
        /**
           \brief Pretty printing (for debugging purposes)

           \remark This procedure will block any thread trying to access the expr_manager.
        */
        void display(std::ostream & out, expr * e, params_ref const & p = params_ref(),
                     unsigned indent = 0, unsigned num_vars = 0, char const * var_prefix = 0) const;
    };

    /**
       \brief Thread safe version of ::mk_pp.
    */
    struct mk_pp {
        expr *               m_expr;
        expr_manager &       m_manager;
        params_ref const &   m_params;
        unsigned             m_indent;
        unsigned             m_num_vars;
        char const *         m_var_prefix;
    public:
        mk_pp(expr * e, expr_manager & m, unsigned indent = 0, unsigned num_vars = 0, char const * var_prefix = 0);
        mk_pp(expr * e, expr_manager & m, params_ref const & p, unsigned indent = 0, unsigned num_vars = 0, char const * var_prefix = 0);
    };

    std::ostream & operator<<(std::ostream & out, mk_pp const & p);
};

#endif
