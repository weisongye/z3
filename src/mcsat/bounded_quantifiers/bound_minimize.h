/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    bound_minimize.h

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-01-24.

--*/
#ifndef _BOUND_MINIMIZE_H_
#define _BOUND_MINIMIZE_H_

#include"bound_info.h"
#include"bound_propagator.h"

class propagate_bound_info
{
private:
    ast_manager & m_m;
    arith_util & m_au;
    bound_propagator m_bp;
    //variables used by m_bp
    sbuffer<bound_propagator::var> m_bp_vars;
    //their corresponding exprs
    expr_ref_buffer m_bp_exprs;
    //variables used for each variables in bi
    sbuffer<bound_propagator::var> m_bp_bi_vars;
    //variables used for each of bounds in bi
    sbuffer<bound_propagator::var> m_bp_bi_bounds;

    bool get_monomial(expr * e,  expr_ref_buffer & terms,  sbuffer<int> & coeffs, int & cval);
    void introduce_var(sort * s, expr_ref & e, bound_propagator::var & var);
    // introduce variable for (x + terms*coeffs), vvar is the variable for x, bvar is the variable for the bound
    void introduce_var(sort * s, expr_ref & x, expr_ref_buffer & terms,  sbuffer<int> & coeffs, bound_propagator::var & vvar, bound_propagator::var & bvar);
public:
    propagate_bound_info(ast_manager& m, arith_util & au, bound_propagator::numeral_manager & nm, bound_propagator::allocator & alloc ) : 
      m_m(m), m_au(au), m_bp( nm, alloc ), m_bp_exprs(m_m){}

    bool compute(bound_info& bi);
    void print( const char * tc );
};

#endif