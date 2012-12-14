/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_default_solver.cpp

Abstract:
        
    MCSAT solver pre-configured with several tactics 
    and components.

Author:

    Leonardo de Moura (leonardo) 2012-12-13.

Revision History:

--*/
#include"mcsat_default_solver.h"
#include"simplify_tactic.h"
#include"nnf_tactic.h"
#include"der_tactic.h"
#include"factor_tactic.h"
#include"tseitin_cnf_tactic.h"
#include"distribute_forall_tactic.h"
#include"elim_term_ite_tactic.h"
#include"ctx_simplify_tactic.h"
#include"propagate_values_tactic.h"
#include"solve_eqs_tactic.h"

namespace mcsat {
    default_solver_factory::default_solver_factory() {
        // This configuration is meaningless at this point.
        // I'm just testing different tactics.
        add_tactic_after(alloc(simplify_tactic_factory));
        add_tactic_after(alloc(propagate_values_tactic_factory));
        add_tactic_after(alloc(solve_eqs_tactic_factory));
        add_tactic_after(alloc(nnf_tactic_factory));
        add_tactic_after(alloc(der_tactic_factory));
        add_tactic_after(alloc(factor_tactic_factory));
        add_tactic_after(alloc(ctx_simplify_tactic_factory));
        add_tactic_after(alloc(tseitin_cnf_tactic_factory));
        add_tactic_after(alloc(distribute_forall_tactic_factory));
        add_tactic_after(alloc(elim_term_ite_tactic_factory));
    }
    
    default_solver_factory::~default_solver_factory() {
    }
};
