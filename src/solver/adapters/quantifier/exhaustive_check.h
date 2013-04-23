/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    exhaustive_check.h

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-04-22.

--*/
#ifndef _EXHAUSTIVE_CHECK_H_
#define _EXHAUSTIVE_CHECK_H_

#include"ast.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"lbool.h"

namespace qsolver
{

class mc_context;
class model_constructor;

class exhaustive_check
{
protected:
    //managers for expressions
    ast_manager & m_m;
    arith_util m_au;
    bv_util m_bvu;
    //helper for exhaustive_instantiate
    bool do_exhaustive_instantiate(mc_context & mc, model_constructor * mct, quantifier * q, ptr_vector<expr> & inst, bool use_rel_domain, expr_ref_buffer & instantiations);
public:
    exhaustive_check(ast_manager & _m);

    //exhaustive instantiate
    lbool run(mc_context & mc, model_constructor * mct, quantifier * q, bool use_rel_domain, expr_ref_buffer & instantiations);
};

}

#endif
