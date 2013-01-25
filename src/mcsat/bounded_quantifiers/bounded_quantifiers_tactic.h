/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    bounded_quantifiers_tactic.h

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-01-17.

--*/
#ifndef _BOUNDED_QUANTIFIERS_TACTIC_H_
#define _BOUNDED_QUANTIFIERS_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_normalize_bounded_quantifiers_tactic(ast_manager & m, params_ref const & p);
tactic * mk_expand_bounded_quantifiers_tactic(ast_manager & m, params_ref const & p);
tactic * mk_minimize_bounded_quantifiers_tactic(ast_manager & m, params_ref const & p);

/*
  ADD_TACTIC("expand_bounded_quantifiers", "expand bounded quantifiers over integer and bit-vector variables.", "mk_expand_bounded_quantifiers_tactic(m, p)")
  ADD_TACTIC("normalize_bounded_quantifiers", "make sure that 0 is the lower bound for variables in bounded quantifiers.", "mk_normalize_bounded_quantifiers_tactic(m, p)")
  ADD_TACTIC("minimize_bounded_quantifiers", "try to minimize the bounds used in bounded quantifiers.", "mk_minimize_bounded_quantifiers_tactic(m, p)")
*/

#endif
