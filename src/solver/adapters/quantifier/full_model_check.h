/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    full_model_check.h

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-04-21.

--*/

#ifndef _FULL_MODEL_CHECK_H_
#define _EVAL_CHECK_H_

#include"model_check.h"

namespace qsolver
{

class full_model_check
{
protected:
    //manager
    ast_manager & m_m;
    arith_util m_au;
    bv_util m_bvu;
    // do simplification?
    bool m_simplification;
    //helper for check, the third argument is an optional mapping from variables to the definitions that should be used for them
    def * do_check(mc_context & mc, model_constructor * mct, quantifier * q, expr * e, ptr_vector<def> & subst);
public:
    full_model_check(ast_manager & _m);
    //check the quantifier
    lbool run(mc_context & mc, model_constructor * mct, quantifier * q, expr_ref_buffer & instantiations, expr_ref_buffer & instantiations_star, bool mk_inst_star);
};

}

#endif
