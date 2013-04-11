/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    expand_macros_tactic.h

Abstract:
    
    Expand simple macros in a goal or assertion stack
    
Author:

    Leonardo de Moura (leonardo) 2013-02-11

Revision History:

--*/
#ifndef _EXPAND_MACROS_TACTIC_H_
#define _EXPAND_MACROS_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_expand_macros_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("expand_macros", "Expand macros defined using universal quantifiers.", "mk_expand_macros_tactic(m, p)")
*/

MK_SIMPLE_TACTIC_FACTORY(expand_macros_tactic_factory, mk_expand_macros_tactic(m, p));

#endif
