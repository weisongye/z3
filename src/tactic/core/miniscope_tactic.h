/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    miniscope_tactic.cpp

Abstract:

    Miniscoping

Author:

    Leonardo de Moura (leonardo) 2013-01-30.

--*/
#ifndef _MINISCOPE_TACTIC_H_
#define _MINISCOPE_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_miniscope_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("miniscope", "Quantifier miniscoping.", "mk_miniscope_tactic(m, p)")
*/

MK_SIMPLE_TACTIC_FACTORY(miniscope_tactic_factory, mk_miniscope_tactic(m, p));

#endif
