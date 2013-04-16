/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    model_check.h

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-04-04.

--*/
#ifndef _CLASSIFY_INFO_H_
#define _CLASSIFY_INFO_H_

#include"ast.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"

namespace qsolver
{

class classify_util
{
protected:
    ast_manager & m_m;
    arith_util & m_au;
    bv_util & m_bvu;
public:
    //requirement enumeration for terms
    enum {
        REQ_NONE,
        REQ_NON_VARIABLE,
        REQ_GROUND
    };
private:
    //internal
    bool is_var_offset(expr * e, var * & v, expr_ref & offset, bool & is_negated, unsigned req, bool mk_offset);
    bool is_var_relation(expr * e, var * & v, expr_ref & t, bool & is_flipped, unsigned req, bool mk_t);
    bool is_witnessable(expr * e, bool hasPolarity, bool polarity, 
                        var * & v1, var * & v2, ptr_vector<expr> & no_proj_terms, expr_ref_buffer & rel_domain, unsigned & proj_type, bool mk_rd, bool req_exact);
public:
    classify_util(ast_manager & m, arith_util & au, bv_util & bvu);
    //is atomic value
    bool is_atomic_value(expr * e);
    //is negated variable
    bool is_var_negated(expr * e, var * & v);
    //is variable
    bool is_var_atom(expr * e);
    bool is_var_atom(expr * e, var * & v, bool & is_negated);
    //is variable with offset?
    bool is_var_offset(expr * e, unsigned req = REQ_NONE);
    bool is_var_offset(expr * e, var * & v, expr_ref & offset, bool & is_negated, unsigned req = REQ_NONE);
    //can e be reformulated as v ~ t for term t meeting requirement "req", 
    //   where ~ is the same kind as e (or flipped)
    bool is_var_relation(expr * e, unsigned req = REQ_NONE);
    bool is_var_relation(expr * e, var * & v, expr_ref & t, bool & is_flipped, unsigned req = REQ_NONE);
    // is witnessable
    bool is_witnessable(expr * e, bool hasPolarity, bool polarity, bool req_exact = true);
    bool is_witnessable(expr * e, bool hasPolarity, bool polarity, 
                        var * & v1, var * & v2, ptr_vector<expr> & no_proj_terms, expr_ref_buffer & rel_domain, unsigned & proj_type, bool req_exact = true);
};

class classify_info
{
protected:
    ast_manager & m_m;
    arith_util & m_au;
    bv_util & m_bvu;
    // use monotonic projections?
    bool m_use_monotonic_projections;
    //the utility object for querying
    classify_util m_util;
    //the quantifier
    quantifier_ref m_q;
    //literals
    expr_ref_buffer m_lits;
    //literals that are model checkable
    ptr_vector<expr> m_mc_lits;
    //literals that are witnessable
    ptr_vector<expr> m_w_lits;
    //classify literal
    void classify_term(expr * e, bool hasPolarity, bool polarity, bool & model_checkable, bool & witnessable, bool & ground_result);
public:
    classify_info(ast_manager & m, arith_util & au, bv_util & bvu, quantifier* q, bool m_use_monotonic_projections = false);
    //compute function
    bool compute();
    //get model-checkable
    void get_model_checkable(expr_ref & e, bool req_witnessable = false);
    //get witnessable
    void get_witnessable(expr_ref & e, bool req_non_model_checkable = false);
    //is completely model checkable
    bool is_model_checkable() { return m_mc_lits.size()==m_lits.size(); }
    //is completely witnessable
    bool is_witnessable() { return m_w_lits.size()==m_lits.size(); }
    //display the classify info
    void display(std::ostream & out);
};


}

#endif
