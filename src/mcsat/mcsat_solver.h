/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_solver.h

Abstract:

    MCSAT solver.

Author:

    Leonardo de Moura (leonardo) 2012-11-01.

Revision History:

--*/
#ifndef _MCSAT_SOLVER_H_
#define _MCSAT_SOLVER_H_

#include"solver.h"
class tactic_factory;

namespace mcsat {
    class plugin;
    class preprocessor;
    class kernel;

    class solver : public ::solver {
        ast_manager &            m_manager;
        scoped_ptr<preprocessor> m_preprocessor;
        scoped_ptr<kernel>       m_kernel;
        friend class solver_factory;
        void commit();
    public:
        solver(ast_manager & m, params_ref const & p, bool produce_proofs, bool produce_models, bool produce_unsat_cores);
        virtual ~solver();
        ast_manager & m() const;
        virtual void collect_param_descrs(param_descrs & r);
        virtual void set_produce_models(bool f);
        virtual void set_progress_callback(progress_callback * callback);
        virtual void updt_params(params_ref const & p);
        virtual void set_cancel(bool f);
        virtual unsigned get_num_assertions() const;
        virtual expr * get_assertion(unsigned idx) const;
        virtual void display(std::ostream & out) const;
        virtual unsigned get_scope_level() const;
        virtual void push();
        virtual void pop(unsigned n);
        virtual void assert_expr(expr * t, expr * a);
        virtual void assert_expr(expr * t);
        virtual lbool check_sat(unsigned num_assumptions, expr * const * assumptions);
        virtual void collect_statistics(statistics & st) const;
        virtual void get_unsat_core(ptr_vector<expr> & r);
        virtual void get_model(model_ref & md);
        virtual proof * get_proof();
        virtual std::string reason_unknown() const;
        virtual void get_labels(svector<symbol> & r);
        void freeze(func_decl * f);
    };

    class solver_factory : public ::solver_factory {
        struct imp;
        imp * m_imp;
    public:
        solver_factory();
        virtual ~solver_factory();
        void add_tactic_before(tactic_factory * f);
        void add_tactic_after(tactic_factory * f);
        void add_plugin(plugin * p);
        virtual ::solver * operator()(ast_manager & m, params_ref const & p, bool proofs_enabled, bool models_enabled, bool unsat_core_enabled, symbol const & logic);
    };

};

#endif
