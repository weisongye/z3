/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_kernel.h

Abstract:

    MCSAT kernel

Author:

    Leonardo de Moura (leonardo) 2012-11-01.

Revision History:

--*/
#ifndef _MCSAT_KERNEL_H_
#define _MCSAT_KERNEL_H_

#include"ast.h"
#include"model.h"
#include"solver.h"
#include"lbool.h"

class statistics;

namespace mcsat {
    class plugin;

    /**
       \brief The kernel implements the search engine in mcsat.
    */
    class kernel : public solver {
        struct imp;
        imp * m_imp;
    public:
        kernel(ast_manager & m, bool proofs_enabled);
        ~kernel();

        void add_plugin(plugin * p);
        
        virtual void assert_expr(expr * f);
        virtual void assert_expr_proof(expr * f, proof * pr);

        virtual void push();
        virtual void pop(unsigned num_scopes);

        virtual lbool check_sat(unsigned num_assumptions, expr * const * assumptions);
        virtual void collect_statistics(statistics & st) const;
        virtual void get_unsat_core(ptr_vector<expr> & r);
        virtual void get_model(model_ref & m);
        virtual proof * get_proof();
        virtual std::string reason_unknown() const;
        
        virtual void set_cancel(bool f);
        virtual void display(std::ostream & out) const;

        // Rest of the Solver API
        virtual void collect_param_descrs(param_descrs & r);
        virtual void set_produce_models(bool f);
        virtual void set_progress_callback(progress_callback * callback);
        virtual void updt_params(params_ref const & p);
        virtual void get_labels(svector<symbol> & r);
    };

};

#endif
