/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    datatypes_quantifiers_tactic.h

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-01-17.

--*/
#ifndef _DATATYPES_QUANTIFIERS_TACTIC_H_
#define _DATATYPES_QUANTIFIERS_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_split_datatype_quantifiers_tactic_core(ast_manager & m, params_ref const & p);
tactic * mk_split_datatype_quantifiers_tactic(ast_manager & m, params_ref const & p);

/*
  ADD_TACTIC("split_datatype_quantifiers", "split datatype quantifiers based on possible constructors.", "mk_split_datatype_quantifiers_tactic(m, p)")
*/

#endif
