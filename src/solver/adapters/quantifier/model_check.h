/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    model_check.h

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-04-02.

--*/
#ifndef _MODEL_CHECK_H_
#define _MODEL_CHECK_H_

#include"ast.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"arith_rewriter.h"
#include"bv_rewriter.h"
#include"region.h"
#include"classify_quantifier.h"
#include"lbool.h"
#include"full_model_check.h"
#include"eval_check.h"

namespace qsolver
{

class inst_trie 
{
protected:
    bool m_data;
    obj_map<expr, inst_trie * > m_inst;
    bool add(mc_context & mc, ptr_vector<expr> & inst, unsigned i);
    bool add(mc_context & mc, expr_ref_buffer & inst, unsigned i);
public:
    inst_trie() : m_data(false){}
    bool add(mc_context & mc, ptr_vector<expr> & inst) { return add(mc, inst, 0); }
    bool add(mc_context & mc, expr_ref_buffer & inst) { return add(mc, inst, 0); }
};

class val;
class v_int;
class v_bv;
class v_expr;
class v_var_offset;

class value_tuple;

class abs_value;
class av_val;
class av_star;
class av_interval;

class cond;

class def;

class model_constructor;
class eval_check;
class full_model_check;

class mc_context
{
    friend class eval_check;
    friend class full_model_check;
protected:
    // do simplification?
    bool m_simplification;
    // do repair
    bool m_model_repairing;
    bool m_model_repairing_recurse;
    //memory manager
    region m_reg;
    //rational manager
    unsynch_mpz_manager m_zm;
    //managers for expressions
    ast_manager & m_m;
    arith_util m_au;
    bv_util m_bvu;
    arith_rewriter m_ar;
    bv_rewriter m_bvr;
    //the utility object for classification questions
    classify_util m_cutil;
protected: //cached information
    // the star abstract value
    av_star * m_star;
    // expressions to values
    obj_map< expr, val * > m_expr_to_val;
    //distinguished values per sort
    obj_map< sort, expr * > m_sort_to_dist_expr;
    //values to abstract values
    ptr_addr_map< val, av_val * > m_val_to_abs_val;
    //values to value tuples
    ptr_addr_map< val, value_tuple * > m_val_to_value_tuple;
    //quantifiers to star conditions
    ptr_addr_map< quantifier, cond * > m_quant_to_cond_star;
    //size to star
    u_map< cond * > m_size_to_star;
    //true and false
    expr * m_true;
    expr * m_false;
    //expressions produced and kept global
    expr_ref_buffer m_expr_produced_global;
    //expressions created by evaluation
    expr_ref_buffer m_expr_produced;
    //new values
    u_map< abs_val * > m_new_vals;
    //instantiations produced
    obj_map<quantifier, inst_trie *> m_inst_trie;
private:
    //evaluate cache
    obj_map< expr, expr * > m_evaluations;
    obj_map< expr, expr * > m_partial_evaluations;
    //
    bool m_evaluation_cache_active;
    //set evaluation cache active
    void set_evaluate_cache_active(bool v) {
        if (v) { 
            m_evaluations.reset(); 
            m_partial_evaluations.reset();
        }
        m_evaluation_cache_active = v;
    }
protected: //helper functions
    //repair model
    bool repair_formula(model_constructor * mct, quantifier * q, expr * e, expr_ref_buffer & vsub, expr_ref_buffer & tsub, bool polarity, 
                        ptr_buffer<annot_entry> & fail_entry, ptr_buffer<expr> & fail_value, ptr_buffer<func_decl> & fail_func, annot_entry * & inst_reason);
    bool repair_term(model_constructor * mct, quantifier * q, expr * t, expr_ref_buffer & vsub, expr_ref_buffer & tsub, expr * v, 
                     ptr_buffer<annot_entry> & fail_entry, ptr_buffer<expr> & fail_value, ptr_buffer<func_decl> & fail_func, annot_entry * & inst_reason);
    expr * ensure_interpretation(model_constructor * mct, expr * t, expr_ref_buffer & vsub, expr_ref_buffer & tsub, 
                                 quantifier * q_reason = 0, annot_entry * inst_reason = 0);
    bool append_entry_to_simple_def(model_constructor * mct, func_decl * f, annot_entry * c, quantifier * q_reason = 0, annot_entry * inst_reason = 0);
    //add instantiation
    bool add_instantiation(model_constructor * mct, quantifier * q, cond * c, expr_ref_buffer & instantiations,
                           bool filterEval = false, bool filterRepair = false, bool filterCache = false);
    bool add_instantiation(model_constructor * mct, quantifier * q, expr_ref_buffer & vsub, expr_ref_buffer & instantiations,
                           bool filterEval = false, bool filterRepair = false, bool filterCache = false);
    bool add_instantiation(model_constructor * mct, quantifier * q, expr_ref_buffer & inst, expr_ref_buffer & vsub, expr_ref_buffer & instantiations,
                           bool filterEval = false, bool filterRepair = false, bool filterCache = false);
    //evaluate function
    val * evaluate_interp(func_decl * f, ptr_buffer<val> & vals);
    expr * evaluate_interp(func_decl * f, expr_ref_buffer & vals);
    //get bound
    val * get_bound(abs_val * a, bool isLower);
    //make value from rational
    val * mk_val(const rational & r);
    //make value from the mpz
    val * mk_val(const mpz & a);
    //make value from rational, bit vector size
    val * mk_val(const rational & r, unsigned bvs);
    //make value from the mpz, bit vector size
    val * mk_val(const mpz & a, unsigned bvs);
    //make variable offset value
    val * mk_val(var * v, val * o, bool isn);
    //make add
    val * mk_add(val * v1, val * v2);
    //make negate
    val * mk_negate(val * v);
    //make a+t from a
    abs_val * mk_offset(abs_val * a, val * v);
    //make -a from a
    abs_val * mk_negate(abs_val * a);
protected: //the following functions are used to translate internally generated values to those that can be used externally
    //mk canon
    val * mk_canon(val * v);
    //mk canon
    value_tuple * mk_canon(value_tuple * vt);
    //mk canon
    abs_val * mk_canon(abs_val * a);
    //mk canon
    cond * mk_canon(cond * c);
public:
    mc_context(ast_manager & _m);
    //reset round
    void reset_round();
    //push user context
    void push();
    //pop user context
    void pop();
    //allocate memory
    void * allocate(size_t size) { return m_reg.allocate(size); }
    //make value from expression
    val * mk_val(expr* e);
    //make offset
    val * mk_offset(val * v1, val * v2);
    //make value tuple from value
    value_tuple * mk_value_tuple(val * v);
    //make value tuple from set of values
    value_tuple * mk_value_tuple(ptr_buffer<val> & vals);
    //make value tuple product
    value_tuple * mk_concat(value_tuple * vt1, value_tuple * vt2);
    //is zero
    bool is_zero(val * v);
    //is v1 less than v2, isLower means null is interpreted as -INF, otherwise it is +INF
    bool is_lt(val * v1, val * v2, bool isLower = true);
    //are two rationals equal
    bool is_eq(const rational & r1, const rational & r2);
    //are two values equal
    bool is_eq(val * v1, val * v2);
    //are two value tuples equal
    bool is_eq(value_tuple * v1, value_tuple * v2);
    //are two abstract values equal
    bool is_eq(abs_val * a1, abs_val * a2);
    //are two conditions equal
    bool is_eq(cond * c1, cond * c2);
    //are two condition compatible
    bool is_compatible(abs_val * a1, abs_val * a2);
    //are two condition compatible
    bool is_compatible(cond * c1, cond * c2);
    //does a1 generalize a2
    bool is_generalization(abs_val * a1, abs_val * a2);
    //does c1 generalize c2
    bool is_generalization(cond * c1, cond * c2);
    //is condition generalization of vector of values
    bool is_generalization(cond * c, ptr_buffer<val> & vals);
    //do meet
    abs_val * mk_meet(abs_val * a1, abs_val * a2);
    //do meet
    cond * mk_meet(cond * c1, cond * c2);
    //do meet, store in tc1
    void do_meet(annot_entry * tc1, annot_entry * tc2);
    //condition make compose
    cond * mk_compose(cond * c1, value_tuple * v, cond * c2);
    //do compose
    bool do_compose(expr_ref_buffer & c1, expr_ref_buffer & v, expr_ref_buffer & e1, annot_entry * c2);
    //make product
    def * mk_product(def * d1, def * d2);
    //make compose
    def * mk_compose(def * df, def * d);
    //do the interpreted compose (modifies d)
    bool do_compose(func_decl * f, def * d);
    //make D_(x~t) from D_t
    def * mk_var_relation(def * d, func_decl * f, var * v, bool is_flipped);
    //make D_(x+t) from D_t
    def * mk_var_offset(def * d, var * v, bool is_negated);
    //mk star
    av_star * mk_star();
    //mk value
    av_val * mk_value(val * v);
    //mk interval
    av_interval * mk_interval(val * l, val * u);
    //mk interval : [l+1 , u]
    av_interval * mk_next_interval(val * l, val * u);
    //mk star
    cond * mk_star(unsigned size);
    //mk star for quantifier
    cond * mk_star(model_constructor * mct, quantifier * q);
    //mk cond
    cond * mk_cond(ptr_buffer<abs_val> & avals);
    //mk cond
    cond * mk_cond(ptr_buffer<val> & vals);
    //mk cond
    cond * mk_cond(annot_entry * tc);
    // copy the condition
    cond * copy(cond * c);
    //make new def
    def * new_def();
    //make annotated entry
    annot_entry * mk_annot_entry(expr_ref_buffer & values, expr_ref_buffer & annotations, expr * result);
    //make annotated entry
    annot_entry * mk_annot_entry(ptr_buffer<expr> & values, ptr_buffer<expr> & annotations, expr * result);
    //make annotated entry
    annot_entry * mk_annot_entry(expr_ref_buffer & values, expr * annotate_t, expr * result);
    //make new def
    simple_def * new_simple_def();
public: //other helper functions
    //get classifier 
    classify_util * get_classify_util() { return &m_cutil; }
    // is atomic value
    bool is_atomic_value(expr * e) { return m_cutil.is_atomic_value(e); }
    //get classify info for quantifier
    //classify_info * get_classify_info(quantifier * q);
    //make distinguished value
    expr * mk_distinguished_constant_expr(sort * s);
    //make some value
    expr * get_some_value(sort * s);
    //make offset subtract
    void mk_offset_sub(expr * e, expr * o, expr_ref & r);
    //make expression from value
    void get_expr_from_val(val * v, expr_ref & e);
    //evaluate
    expr * evaluate(model_constructor * mct, expr * e, expr_ref_buffer & vsub, bool partial = false);
    expr * evaluate(model_constructor * mct, expr * e, bool partial = false);
public: //display functions
    //display the expression
    void display(std::ostream & out, expr * e);
    //display the value
    void display(std::ostream & out, val * v);
    //display the abstract value
    void display(std::ostream & out, abs_val * av);
    //display the tuple of values
    void display(std::ostream & out, value_tuple * vt);
    //display the condition (tuple of abstract values)
    void display(std::ostream & out, cond * c);
    //display the entry
    void display(std::ostream & out, cond * c, val * v);
    void display(std::ostream & out, cond * c, value_tuple * vt);
    //display the term condition
    void display(std::ostream & out, annot_entry * c);
    //display the definition
    void display(std::ostream & out, def * d);
    void display(std::ostream & out, simple_def * d);
};

}

#endif
