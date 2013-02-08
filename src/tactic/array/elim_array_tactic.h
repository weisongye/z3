/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    elim_array_tactic.h

Abstract:
    
    Eliminate array terms using unintepreted functions
    
Author:

    Leonardo de Moura (leonardo) 2013-02-07

Revision History:

--*/
#ifndef _ELIM_ARRAY_TACTIC_H_
#define _ELIM_ARRAY_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_elim_array_tactic(ast_manager & m, params_ref const & p);

/*
  ADD_TACTIC("elim_array", "Reduce array theory to EUF.", "mk_elim_array_tactic(m, p)")
*/

MK_SIMPLE_TACTIC_FACTORY(elim_array_tactic_factory, mk_elim_array_tactic(m, p));

#endif
