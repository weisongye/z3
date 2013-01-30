/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    expand_bounded_quantifiers_tactic.h

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-01-29.

--*/
#ifndef _EXPAND_BOUNDED_QUANTIFIERS_TACTIC_H_
#define _EXPAND_BOUNDED_QUANTIFIERS_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_expand_bounded_quantifiers_tactic(ast_manager & m, params_ref const & p);

/*
  ADD_TACTIC("expand_bounded_quantifiers", "expand bounded quantifiers over integer and bit-vector variables.", "mk_expand_bounded_quantifiers_tactic(m, p)")
*/

#endif
