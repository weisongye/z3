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
#include"mpq.h"
#include"classify_quantifier.h"
#include"lbool.h"

namespace qsolver
{

class mc_context;

//values
class v_int;
class v_bv;
class v_expr;

class val
{
protected:
    unsigned m_kind;
    val(unsigned k) : m_kind(k){}
public:
    enum {
        KIND_INT,
        KIND_BV,
        KIND_EXPR,
        KIND_VAR_OFFSET
    };
    //get kind
    unsigned get_kind() { return m_kind; }
    bool is_int() { return m_kind==KIND_INT; }
    bool is_bv() { return m_kind==KIND_BV; }
    bool is_expr() { return m_kind==KIND_EXPR; }
    bool is_var_offset() { return m_kind==KIND_VAR_OFFSET; }
};

class v_int : public val {
    friend class mc_context;
protected:
    mpz m_value;
    v_int() : val(KIND_INT) {}
public:
    mpz const & get_value() const { return m_value; }
};

class v_bv : public val {
    friend class mc_context;
protected:
    mpz m_value;
    unsigned m_size;
    v_bv(unsigned sz) : val(KIND_BV), m_size(sz) {}
public:
    mpz const & get_value() const { return m_value; }
    unsigned get_size() { return m_size; }
};

class v_expr : public val {
    friend class mc_context;
protected:
    expr * m_value;
    v_expr(expr * v) : val(KIND_EXPR), m_value(v) {}
public:
    expr * get_value() { return m_value; }
};

//variable with offset
class v_var_offset : public val {
    friend class mc_context;
protected:
    var * m_var;
    val * m_offset;   // if null, then offset is zero
    bool m_is_negated;
    v_var_offset(var * v, val * o, bool isn) : val(KIND_VAR_OFFSET), m_var(v), m_offset(o), m_is_negated(isn) {}
public:
    var * get_variable() { return m_var; }
    val * get_offset() { return m_offset; }
    bool get_is_negated() { return m_is_negated; }
};

inline v_int * to_int(val * v) {
    SASSERT(v->get_kind()==val::KIND_INT);
    return static_cast<v_int *>(v);
}

inline v_bv * to_bv(val * v) {
    SASSERT(v->get_kind()==val::KIND_BV);
    return static_cast<v_bv *>(v);
}

inline v_expr * to_expr(val * v) {
    SASSERT(v->get_kind()==val::KIND_EXPR);
    return static_cast<v_expr *>(v);
}

inline v_var_offset * to_var_offset(val * v) {
    SASSERT(v->get_kind()==val::KIND_VAR_OFFSET);
    return static_cast<v_var_offset *>(v);
}

//tuple of values
class value_tuple {
    friend class mc_context;
protected:
    //the data
    unsigned m_size;
    val * m_vec[];
    value_tuple( unsigned sz ) : m_size(sz) {}
    static value_tuple * mk(mc_context & mc, unsigned arity );
public:
    unsigned get_size() { return m_size; }
    val * get_value(unsigned i) { return m_vec[i]; }
};


//abstract values
class av_val;
class av_interval;
class av_star;

class abs_val {
protected:
    unsigned m_kind;
    abs_val(unsigned k) : m_kind(k){}
public:
    enum {
        KIND_VAL,
        KIND_INTERVAL,
        KIND_STAR
    };
    //get kind
    unsigned get_kind() { return m_kind; }
    bool is_value() { return m_kind==KIND_VAL; }
    bool is_interval() { return m_kind==KIND_INTERVAL; }
    bool is_star() { return m_kind==KIND_STAR; }
};

class av_val : public abs_val {
    friend class mc_context;
protected:
    val * m_value;
    av_val(val * v) : abs_val(KIND_VAL), m_value( v ) {}
public:
    val * get_value() { return m_value; }
};

class av_interval : public abs_val {
    friend class mc_context;
protected:
    val * m_lower;  // if null, then lower is -INF
    val * m_upper;  // if null, then upper is +INF
    av_interval(val * l, val* u) : abs_val(KIND_INTERVAL), m_lower(l), m_upper(u){}
public:
    val * get_lower() { return m_lower; }
    val * get_upper() { return m_upper; }
};

class av_star : public abs_val {
    friend class mc_context;
protected:
    av_star() : abs_val(KIND_STAR) {}
public:
};

inline av_val * to_value(abs_val * v) {
    SASSERT(v->get_kind()==abs_val::KIND_VAL);
    return static_cast<av_val*>(v);
}
inline av_interval * to_interval(abs_val * v) {
    SASSERT(v->get_kind()==abs_val::KIND_INTERVAL);
    return static_cast<av_interval*>(v);
}
inline av_star * to_star(abs_val * v) {
    SASSERT(v->get_kind()==abs_val::KIND_STAR);
    return static_cast<av_star*>(v);
}

//condition (tuple of abstract values)
class cond {
    friend class mc_context;
protected:
    //the data
    unsigned m_size;
    abs_val * m_vec[];
    cond(unsigned sz) : m_size(sz) {}
    static cond * mk(mc_context & mc, unsigned arity);
public:
    //get the size of the condition
    unsigned get_size() { return m_size; }
    //get the value at index
    abs_val * get_value(unsigned i) { return m_vec[i]; }
    //is this condition a tuple of values
    bool is_value();
    //is this condition a tuple of *'s
    bool is_star();
};

//trie of values
class cond_generalization_trie 
{
private:
    ptr_addr_map< abs_val, cond_generalization_trie * > m_children;
    bool has_generalization(mc_context & mc, cond * c, unsigned index, abs_val * star);
    bool add(mc_context & mc, cond * c, unsigned index, abs_val * star);
public:
    bool add(mc_context & mc, cond * c);
};


//definition (a list of entries)
class def {
    friend class mc_context;
protected:
    ptr_vector<cond> m_conds;
    ptr_vector<value_tuple> m_values;
    //index for indexing conditions
    cond_generalization_trie m_cgt;
    //is there a generalization of c already in this definition
    bool has_generalization(mc_context & mc, cond * c);
public:
    unsigned get_num_entries() { return m_conds.size(); }
    cond * get_condition(unsigned i) { return m_conds[i]; }
    value_tuple * get_value(unsigned i) { return m_values[i]; }
    //add entry to the definition
    bool append_entry(mc_context & mc, cond * c, value_tuple * val);
    //c should be a ground condition
    value_tuple * evaluate(mc_context & mc, cond * c);
    //simplify the definition
    void simplify(mc_context & mc);
};

class model_constructor;

class mc_context
{
protected:
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
    av_star m_star;
    // expressions to values
    obj_map< expr, val * > m_expr_to_val;
    //distinguished values per sort
    obj_map< sort, expr * > m_sort_to_dist_expr;
    //values to abstract values
    ptr_addr_map< val, av_val * > m_val_to_abs_val;
    //quantifiers to star conditions
    ptr_addr_map< quantifier, cond * > m_quant_to_cond_star;
    //true and false
    expr * m_true;
    expr * m_false;
    //expressions produced and kept global
    expr_ref_buffer m_expr_produced_global;
    //expressions created by evaluation
    expr_ref_buffer m_expr_produced;
    //new values
    u_map< abs_val * > m_new_vals;
protected: //helper functions
    //helper for check, the third argument is an optional mapping from variables to the definitions that should be used for them
    def * do_check(model_constructor * mct, quantifier * q, expr * e, ptr_vector<def> & subst);
    //helper for exhaustive_instantiate
    bool do_exhaustive_instantiate(model_constructor * mct, quantifier * q, ptr_vector<expr> & inst, bool use_rel_domain);
    //evaluate function
    val * evaluate(func_decl * f, ptr_vector<val> & vals);
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
    //do meet
    abs_val * mk_meet(abs_val * a1, abs_val * a2);
    //do meet
    cond * mk_meet(cond * c1, cond * c2);
    //condition make compose
    cond * mk_compose(cond * c1, value_tuple * v, cond * c2);
    //make product
    def * mk_product(def * d1, def * d2);
    //make compose
    def * mk_compose(def * df, def * d);
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
    //mk value at index
    //cond * mk_value_at_index(abs_val * a, unsigned index, unsigned size);
    //mk cond
    cond * mk_cond(ptr_buffer<abs_val> & avals);
    // copy the condition
    cond * copy(cond * c);
    //make new def
    def * new_def();
public: //other helper functions
    //get classifier 
    classify_util * get_classify_util() { return &m_cutil; }
    // is atomic value
    bool is_atomic_value(expr * e) { return m_cutil.is_atomic_value(e); }
    //make distinguished value
    expr * mk_distinguished_constant_expr(sort * s);
    //make some value
    expr * get_some_value(sort * s);
    //make offset subtract
    void mk_offset_sub(expr * e, expr * o, expr_ref & r);
    //make expression from value
    void get_expr_from_val(val * v, expr_ref & e);
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
    //display the definition
    void display(std::ostream & out, def * d );
public:
    //check the quantifier
    lbool check(model_constructor * mct, quantifier * q, expr_ref_buffer & instantiations);
    //exhaustive instantiate
    bool exhaustive_instantiate(model_constructor * mct, quantifier * q, bool use_rel_domain = true);
};

}

#endif
