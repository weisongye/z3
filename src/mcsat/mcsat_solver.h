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

namespace mcsat {

    class solver : public ::solver {
        struct imp;
        imp * m_imp;

    public:
        solver();
        ~solver();

        virtual void updt_params(params_ref const & p);
        virtual void collect_param_descrs(param_descrs & r);
        
        virtual void set_produce_proofs(bool f);
        virtual void set_produce_models(bool f);
        virtual void set_produce_unsat_cores(bool f);

        virtual void init(ast_manager & m, symbol const & logic);

        virtual void reset();

        virtual void assert_expr(expr * t);
        virtual void push();
        virtual void pop(unsigned n);
        virtual unsigned get_scope_level() const;

        virtual lbool check_sat(unsigned num_assumptions, expr * const * assumptions);
        virtual void collect_statistics(statistics & st) const;
        virtual void get_unsat_core(ptr_vector<expr> & r);
        virtual void get_model(model_ref & m);
        virtual proof * get_proof();
        virtual std::string reason_unknown() const;
        virtual void get_labels(svector<symbol> & r);

        virtual void set_cancel(bool f);

        virtual void set_progress_callback(progress_callback * callback);
        virtual unsigned get_num_assertions() const;
        virtual expr * get_assertion(unsigned idx) const;
        virtual void display(std::ostream & out) const;
    };
};

#endif
