/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    normalize_bounded_quantifiers_tactic.h

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-01-17.

--*/
#ifndef _NORMALIZE_BOUNDED_QUANTIFIERS_TACTIC_H_
#define _NORMALIZE_BOUNDED_QUANTIFIERS_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_normalize_bounded_quantifiers_tactic_core(ast_manager & m);
tactic * mk_normalize_bounded_quantifiers_tactic(ast_manager & m);

/*
  ADD_TACTIC("normalize_bounded_quantifiers", "make sure that 0 is the lower bound for variables in bounded quantifiers.", "mk_normalize_bounded_quantifiers_tactic(m)")
*/

#endif
