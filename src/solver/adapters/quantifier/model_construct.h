/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    model_construct.h

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-04-02.

--*/
#ifndef _MODEL_CONSTRUCT_H_
#define _MODEL_CONSTRUCT_H_

#include"model_check.h"

namespace qsolver
{

class projection
{
public:
    enum {
        PROJ_POINTWISE, //the default
        PROJ_MONOTONIC,
    };
protected:
    projection * m_find;
    unsigned m_type;
    ptr_vector<expr> m_rel_domain_pre;
    //the computed relevant domain
    ptr_vector<expr> m_rel_domain;
    ptr_vector<val> m_rel_domain_val;
    ptr_addr_map<val, unsigned> m_rel_domain_val_ind;
    //for pointwise projection
    expr * m_projection_term;
    ptr_vector<expr> m_no_projection_terms;
    val * m_projection_term_val;
    //for monotonic projection
    ptr_vector<av_interval> m_monotonic_intervals;
    //offset
    expr * m_offset;
    bool m_offset_valid;

    expr * m_last_projection_term;
protected:
    void compute(mc_context & mc);
public:
    projection();
    //reset
    void reset();
    //merge
    void merge(projection * p);
    //merge with offset
    bool merge_with_offset(projection * p, expr * o);
    //get rep
    projection * get_rep();
    //set projection type
    void set_projection_type(unsigned typ) { m_type = typ; }
    //get projection type
    unsigned get_projection_type() { return m_type; }
    //set projection term (for pointwise projection)
    void set_projection_term(expr * e);
    //set no projection term (for pointwise projection)
    void add_no_projection_term(expr * e);
    //add to relevant domain (value unknown)
    void add_relevant_domain(expr * e);
    //add to relevant domain with known value
    void add_relevant_domain(expr * e, val * v);
public:
    //assert the partial model
    void assert_partial_model(mc_context & mc, obj_map< expr, expr * > & m, sort * s);
    //get projection term
    expr * get_projection_term() { return m_projection_term; }
    //get projected value
    abs_val * get_projected_value(mc_context & mc, val * v);
    //get the final default
    abs_val * get_projected_default(mc_context & mc);
    //get offset
    expr * get_offset() { return m_offset; }
    //get witness : o is the offset 
    void get_witness(mc_context & mc, abs_val * a, expr_ref & e, expr * o, sort * s, bool & found_expr);
    //get relevant domain size
    unsigned get_num_relevant_domain() { return m_rel_domain.size(); }
    //get relevant domain 
    expr * get_relevant_domain(unsigned i) { return m_rel_domain[i]; }
    //get relevant domain value
    val * get_relevant_domain_val(unsigned i) { return m_rel_domain_val[i]; }
    //compute intervals helper function
    static void compute_intervals(mc_context & mc, ptr_vector<val> & vals, ptr_vector<av_interval> & intervals);
protected: //TEMPORARY? debugging, for explicit projection construction
    //map from eqc id to projection function
    def * m_proj_def;
public:
    //get the projection for the ith argument of f
    def * get_definition(mc_context & mc);
};


class model_constructor
{
public:
    // use monotonic projections?
    bool m_monotonic_projections;
    // do simplification?
    bool m_simplification;
protected:
    //function to id map
    obj_map< func_decl, unsigned > m_func_to_id;
    //functions
    ptr_vector< func_decl > m_funcs;
    //map from func id to projections
    u_map< ptr_vector<projection> > m_func_arg_proj;
    //get function id
    unsigned get_func_id(mc_context & mc, func_decl * f);

    //map from quantifiers to id
    obj_map<quantifier, unsigned> m_quant_to_id;
    //quantifiers
    ptr_vector< quantifier > m_quants;
    //map from quantifier id to projections
    u_map< ptr_vector<projection> > m_quant_var_proj;
    //get quantifier id
    unsigned get_quantifier_id(mc_context & mc, quantifier * q);

    //partial definitions reflecting ground assertions
    u_map< def * > m_ground_def;
    //complete definitions
    u_map< def * > m_def;
    //terms that need to be in the partial model
    expr_ref_buffer m_partial_model_terms;
    //universe for uninterpreted sorts
    obj_map< sort, ptr_vector<expr> > m_universe;
protected:
    //managers for expressions
    ast_manager & m_m;
    arith_util m_au;
    bv_util m_bvu;
protected:
    //process the body of a quantifier
    void process(mc_context & mc, expr * e, ptr_vector<projection> & var_proj, bool hasPolarity, bool polarity);
    //construct entries function
    void construct_entries(mc_context & mc, func_decl * f, def * dg, sbuffer<unsigned> & order_indices, 
                           sbuffer<unsigned> & process_entries, ptr_buffer<abs_val> & avals,
                           def * d);
    //add term to relevant domain of projection
    void add_relevant_domain(projection * p, expr * e);
public:
    //constructor
    model_constructor(ast_manager & _m, bool use_monotonic_projections = false);
    //do these 5 things in the following order before calling get_def:
    //reset the round
    void reset_round(mc_context & mc);
    //assert quantifier
    void assert_quantifier(mc_context & mc, quantifier * q);
    //(optional) set projection term: if t if f(t1...tn), then t1...tn used as projection term for f's projection terms (or per argument)
    void set_projection_term(mc_context & mc, expr * t);
    void set_projection_term(mc_context & mc, func_decl * f, unsigned i, expr * e);
    //determine the terms that must be in the parial model
    unsigned get_num_partial_model_terms() { return m_partial_model_terms.size(); }
    expr * get_partial_model_term(unsigned i) { return m_partial_model_terms[i]; }
    //assert the partial model
    void assert_partial_model(mc_context & mc, obj_map< expr, expr * > & m);
public:
    //push user context
    void push();
    //pop user context
    void pop();
public:
    //get projection
    projection * get_projection(mc_context & mc, func_decl * f, unsigned i, bool mk_rep = true);
    //get projection
    projection * get_projection(mc_context & mc, quantifier * q, unsigned i, bool mk_rep = true);
    //get number of functions
    unsigned get_num_functions() { return m_funcs.size(); }
    //get function at index
    func_decl * get_function(unsigned i) { return m_funcs[i]; }
    //get the definition for function
    def * get_ground_def(mc_context & mc, func_decl * f);
    //get the complete definition for function
    def * get_def(mc_context & mc, func_decl * f);
    //get universe size
    unsigned get_num_universe(sort * s);
    //get universe 
    expr * get_universe(mc_context & mc, sort * s, unsigned i);
    //get term vector to instantiate q with, based on condition c
    void get_inst(mc_context & mc, quantifier * q, cond * c, expr_ref_buffer & inst, bool & found_expr);
protected: //TEMPORARY? debugging, for explicit projection construction
    //use projections explicitly
    bool m_projection_definitions;
    //map from func id to projection function
    u_map< def * > m_projections;
public:
    //get the projection definition for f
    def * get_projection_definition(mc_context & mc, func_decl * f);
};



}

#endif
