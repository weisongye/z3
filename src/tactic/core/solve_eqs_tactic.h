/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    solve_eqs_tactic.h

Abstract:

    Tactic for solving equations and performing gaussian elimination.

Author:

    Leonardo de Moura (leonardo) 2011-12-29.

Revision History:

--*/
#ifndef _SOLVE_EQS_TACTIC_H_
#define _SOLVE_EQS_TACTIC_H_

#include"params.h"
#include"tactic.h"
class expr_replacer;

tactic * mk_solve_eqs_tactic(ast_manager & m, params_ref const & p = params_ref(), expr_replacer * r = 0);

/*
  ADD_TACTIC("solve_eqs", "eliminate variables by solving equations.", "mk_solve_eqs_tactic(m, p)")
*/

MK_SIMPLE_TACTIC_FACTORY(solve_eqs_tactic_factory, mk_solve_eqs_tactic(m, p));

#endif

