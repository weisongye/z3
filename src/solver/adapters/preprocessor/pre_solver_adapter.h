/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    pre_solver_adapter.h

Abstract:

    Add preprocessing capabilities to an existing solver.

Author:

    Leonardo de Moura (leonardo) 2012-11-01.

Revision History:

--*/
#ifndef _PRE_SOLVER_ADAPTER_H_
#define _PRE_SOLVER_ADAPTER_H_

#include"solver.h"
class tactic_factory;

class pre_solver_adapter : public solver {
    struct imp;
    imp *  m_imp;
    friend class pre_solver_adapter_factory;
public:
    pre_solver_adapter(ast_manager & m, core_solver * s, params_ref const & p, bool produce_proofs, bool produce_models, bool produce_unsat_cores);
    virtual ~pre_solver_adapter();
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
    virtual void assert_expr(expr * t);
    virtual void assert_expr_assumption(expr * t, expr * a);
    virtual void assert_expr_proof(expr * t, proof * pr);
    virtual lbool check_sat(unsigned num_assumptions, expr * const * assumptions);
    virtual void collect_statistics(statistics & st) const;
    virtual void get_unsat_core(ptr_vector<expr> & r);
    virtual void get_model(model_ref & md);
    virtual proof * get_proof();
    virtual std::string reason_unknown() const;
    virtual void get_labels(svector<symbol> & r);
    void freeze(func_decl * f);
};

/**
   \brief Abstract class for creating factories for solvers based on pre_solver_adapter_factory.
*/
class pre_solver_adapter_factory : public solver_factory {
    struct imp;
    imp * m_imp;
protected:
    virtual pre_solver_adapter * mk_solver(ast_manager & m, params_ref const & p, bool proofs_enabled, bool models_enabled, bool unsat_core_enabled, symbol const & logic) = 0;
public:
    pre_solver_adapter_factory();
    virtual ~pre_solver_adapter_factory();
    void add_tactic_before(tactic_factory * f);
    void add_tactic_after(tactic_factory * f);
    virtual solver * operator()(ast_manager & m, params_ref const & p, bool proofs_enabled, bool models_enabled, bool unsat_core_enabled, symbol const & logic);
};

#endif
