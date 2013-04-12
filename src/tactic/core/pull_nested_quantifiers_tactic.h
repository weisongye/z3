/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    pull_nested_quantifiers_tactic.h

Abstract:

    Pull nested quantifiers.

Author:

    Leonardo (leonardo) 2013-04-11

Notes:

--*/
#ifndef __PULL_NESTED_QUANTIFIERS_TACTIC_H_
#define __PULL_NESTED_QUANTIFIERS_TACTIC_H_

#include"params.h"
class tactic;
class ast_manager;

tactic * mk_pull_nested_quantifiers_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("pull_nested_quantifiers", "pull nested quantifiers.", "mk_pull_nested_quantifiers_tactic(m, p)")
*/

#endif
