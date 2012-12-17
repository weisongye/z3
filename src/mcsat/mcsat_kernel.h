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
#include"lbool.h"

class statistics;

namespace mcsat {
    class plugin;

    /**
       \brief The kernel implements the search engine in mcsat.
    */
    class kernel {
        struct imp;
        imp * m_imp;
    public:
        kernel(ast_manager & m, bool proofs_enabled);
        ~kernel();

        void add_plugin(plugin * p);
        
        void assert_expr(expr * f, proof * pr, expr_dependency * d);

        void push();
        void pop(unsigned num_scopes);

        lbool check_sat(unsigned num_assumptions, expr * const * assumptions);
        void collect_statistics(statistics & st) const;
        void get_unsat_core(ptr_vector<expr> & r);
        void get_model(model_ref & m);
        proof * get_proof();
        std::string reason_unknown() const;

        void set_cancel(bool f);
        void display(std::ostream & out) const;
    };

};

#endif
