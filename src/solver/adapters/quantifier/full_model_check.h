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
#define _FULL_MODEL_CHECK_H_

#include"ast.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"mpq.h"
#include"lbool.h"

namespace qsolver
{

class mc_context;
class model_constructor;

//values
class val
{
    friend class mc_context;
protected:
    expr * m_expr;
    unsigned m_kind;
    val(unsigned k, expr * e = 0) : m_expr(e), m_kind(k){}
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
    v_expr(expr * v) : val(KIND_EXPR, v) {}
public:
    expr * get_value() { return m_expr; }
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
    unsigned m_data;
    ptr_addr_map< abs_val, cond_generalization_trie * > m_children;
    bool has_generalization(mc_context & mc, cond * c, unsigned index, abs_val * star);
    bool add(mc_context & mc, cond * c, unsigned index, abs_val * star, unsigned data_val);
    bool evaluate(mc_context & mc, cond * c, unsigned index, unsigned & data_val);
    bool evaluate(mc_context & mc, ptr_buffer<abs_val> & vals, unsigned index, unsigned & data_val);
    bool evaluate(mc_context & mc, ptr_buffer<val> & vals, unsigned index, unsigned & data_val);
public:
    cond_generalization_trie() : m_data(0) {}
    bool add(mc_context & mc, cond * c, unsigned data_val);
    bool evaluate(mc_context & mc, cond * c, unsigned & data_val) { return evaluate(mc, c, 0, data_val); }
    bool evaluate(mc_context & mc, ptr_buffer<abs_val> & vals, unsigned & data_val) { return evaluate(mc, vals, 0, data_val); }
    bool evaluate(mc_context & mc, ptr_buffer<val> & vals, unsigned & data_val) { return evaluate(mc, vals, 0, data_val); }
};


class def
{
    friend class mc_context;
protected:
    bool m_has_simplified;
    ptr_vector<cond> m_conds;
    ptr_vector<value_tuple> m_values;
    //index for indexing conditions
    cond_generalization_trie m_cgt;
    def() : m_has_simplified(false) {}
public:
    unsigned get_num_entries() { return m_conds.size(); }
    cond * get_condition(unsigned i) { return m_conds[i]; }
    value_tuple * get_value(unsigned i) { return m_values[i]; }
    //add entry to the definition
    bool append_entry(mc_context & mc, cond * c, value_tuple * val);
    //c should be a ground condition
    value_tuple * evaluate(mc_context & mc, cond * c, bool ignore_else = false);
    value_tuple * evaluate(mc_context & mc, ptr_buffer<val> & vals, bool ignore_else = false);
    //simplify the definition
    void simplify(mc_context & mc);
};


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
