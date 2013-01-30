/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    minimize_bounded_quantifiers_tactic.h

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-01-17.

--*/
#ifndef _MINIMIZE_BOUNDED_QUANTIFIERS_TACTIC_H_
#define _MINIMIZE_BOUNDED_QUANTIFIERS_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_minimize_bounded_quantifiers_tactic(ast_manager & m, params_ref const & p);

/*
  ADD_TACTIC("minimize_bounded_quantifiers", "try to minimize the bounds used in bounded quantifiers.", "mk_minimize_bounded_quantifiers_tactic(m, p)")
*/

#endif
