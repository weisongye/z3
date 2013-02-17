/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    elim_patterns_tactic.h

Abstract:

    Eliminate pattern annotations in the code.

Author:

    Leonardo de Moura (leonardo) 2013-02-17.

--*/
#ifndef _ELIM_PATTERNS_TACTIC_H_
#define _ELIM_PATTERNS_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_elim_patterns_tactic(ast_manager & m, params_ref const & p);

/*
  ADD_TACTIC("elim_patterns", "Eliminate pattern annotations.", "mk_elim_patterns_tactic(m, p)")
*/

MK_SIMPLE_TACTIC_FACTORY(elim_patterns_tactic_factory, mk_elim_patterns_tactic(m, p));

#endif
