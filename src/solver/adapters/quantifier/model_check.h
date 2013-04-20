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
    unsigned m_kind;
    ptr_vector<cond> m_conds;
    ptr_vector<value_tuple> m_values;
    //index for indexing conditions
    cond_generalization_trie m_cgt;
    def(unsigned k) : m_kind(k){}
public:
    enum {
        KIND_COMPLETE,
        KIND_SIMPLE
    };
    //get kind
    unsigned get_kind() { return m_kind; }
    bool is_complete() { return m_kind==KIND_COMPLETE; }
    bool is_simple() { return m_kind==KIND_SIMPLE; }
public:
    virtual unsigned get_num_entries() = 0;
    virtual cond * get_condition(unsigned i) = 0;
    virtual value_tuple * get_value(unsigned i) = 0;
    //add entry to the definition
    virtual bool append_entry(mc_context & mc, cond * c, value_tuple * val) = 0;
    //c should be a ground condition
    virtual value_tuple * evaluate(mc_context & mc, cond * c) = 0;
    virtual value_tuple * evaluate(mc_context & mc, ptr_buffer<val> & vals) = 0;
    virtual void simplify(mc_context & mc) = 0;
};

//definition (a list of entries)
class complete_def : public def {
    friend class mc_context;
protected:
    // for debugging
    bool has_simplified;
public:
    complete_def() : def(KIND_COMPLETE), has_simplified(false){}
    unsigned get_num_entries() { return m_conds.size(); }
    cond * get_condition(unsigned i) { return m_conds[i]; }
    value_tuple * get_value(unsigned i) { return m_values[i]; }
    //add entry to the definition
    bool append_entry(mc_context & mc, cond * c, value_tuple * val);
    //c should be a ground condition
    value_tuple * evaluate(mc_context & mc, cond * c);
    value_tuple * evaluate(mc_context & mc, ptr_buffer<val> & vals);
    //value_tuple * evaluate(mc_context & mc, ptr_buffer<abs_val> & vals);
    //simplify the definition
    void simplify(mc_context & mc);
};

class simple_def : public def
{
    friend class mc_context;
protected:
    cond * m_cond_else;
    value_tuple * m_else;
public:
    simple_def() : def(KIND_SIMPLE), m_else(0) {}
    unsigned get_num_entries() { return m_conds.size()+(m_else ? 1 : 0); }
    cond * get_condition(unsigned i) { return i==m_conds.size() ? m_cond_else : m_conds[i]; }
    value_tuple * get_value(unsigned i) { return i==m_values.size() ? m_else : m_values[i]; }
    void set_else(cond * ce, value_tuple * ve) { m_cond_else = ce; m_else = ve; }
    value_tuple * get_else() { return m_else; }
    //add entry to the definition
    bool append_entry(mc_context & mc, cond * c, value_tuple * v);
    //c should be a ground condition
    value_tuple * evaluate(mc_context & mc, cond * c);
    value_tuple * evaluate(mc_context & mc, ptr_buffer<val> & vals);
    //simplify the definition
    void simplify(mc_context & mc) {}
};


inline complete_def * to_complete(def * d) {
    SASSERT(d->get_kind()==def::KIND_COMPLETE);
    return static_cast<complete_def *>(d);
}

inline simple_def * to_simple(def * d) {
    SASSERT(d->get_kind()==def::KIND_SIMPLE);
    return static_cast<simple_def *>(d);
}


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


class eval_node
{
    friend class mc_context;    //temporary
private:
    expr * m_e;
    //def * m_value;
    val * m_value;
    ptr_vector<eval_node> m_parents;
    ptr_vector<eval_node> m_children;
    unsigned m_children_eval_count;
    unsigned m_vars_to_bind;
public:
    eval_node(expr * e) : m_e(e), m_value(0), m_children_eval_count(0), m_vars_to_bind(0) {}

    expr * get_expr() { return m_e; }
    void add_parent(eval_node * p) { 
        m_parents.push_back(p); 
        p->m_children.push_back(this);
    }
    unsigned get_num_children() { return m_children.size(); }
    eval_node * get_child(unsigned i) { return m_children[i]; }
    void notify_evaluation(ptr_vector<eval_node> & active);
    void unnotify_evaluation();
    val * get_evaluation() { return m_value; }
    bool can_evaluate() { return is_app(m_e) && m_children_eval_count==to_app(m_e)->get_num_args(); }
};



class model_constructor;

class mc_context
{
protected:
    // do simplification?
    bool m_simplification;
    // do partial evaluation
    bool m_partial_evaluation;
    // do repair
    bool m_model_repairing;
    // do instantiation limiting
    bool m_eval_check_inst_limited;
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
    obj_map< quantifier, inst_trie * > m_inst_trie;
protected: //helper functions
    //helper for check, the third argument is an optional mapping from variables to the definitions that should be used for them
    def * do_check(model_constructor * mct, quantifier * q, expr * e, ptr_vector<def> & subst);
    //helper for exhaustive_instantiate
    bool do_exhaustive_instantiate(model_constructor * mct, quantifier * q, ptr_vector<expr> & inst, bool use_rel_domain, expr_ref_buffer & instantiations);
    //evaluate
    val * evaluate(model_constructor * mct, expr * e, ptr_buffer<val> & vsub, bool add_entries_ensuring_non_star = false);
    val * evaluate(model_constructor * mct, expr * e, bool add_entries_ensuring_non_star = false);
    //repair model
    bool repair_formula(model_constructor * mct, quantifier * q, expr * e, ptr_buffer<val> & vsub, expr_ref_buffer & tsub, bool polarity);
    bool repair_term(model_constructor * mct, quantifier * q, expr * t, ptr_buffer<val> & vsub, expr_ref_buffer & tsub, val * v);
    //add instantiation
    bool add_instantiation(model_constructor * mct, quantifier * q, cond * c, expr_ref_buffer & instantiations, bool & repaired,
                           bool filterEval = false, bool filterRepair = false, bool filterCache = false);
    bool add_instantiation(model_constructor * mct, quantifier * q, ptr_buffer<val> & vsub, expr_ref_buffer & instantiations, bool & repaired,
                           bool filterEval = false, bool filterRepair = false, bool filterCache = false);
    bool add_instantiation(model_constructor * mct, quantifier * q, expr_ref_buffer & inst, ptr_buffer<val> & vsub, expr_ref_buffer & instantiations, bool & repaired,
                           bool filterEval = false, bool filterRepair = false, bool filterCache = false);
    bool add_instantiation(model_constructor * mct, quantifier * q, cond * c, expr_ref_buffer & instantiations, bool filterEval = false) {
        bool repaired;
        return add_instantiation(mct,q,c,instantiations,repaired, filterEval, false);
    }
    //evaluate function
    val * evaluate_interp(func_decl * f, ptr_buffer<val> & vals);
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
    //condition make compose
    cond * mk_compose(cond * c1, value_tuple * v, cond * c2);
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
    // copy the condition
    cond * copy(cond * c);
    //make new def
    complete_def * new_complete_def();
    //make new def
    simple_def * new_simple_def();
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
    //display the entry
    void display(std::ostream & out, cond * c, val * v);
    void display(std::ostream & out, cond * c, value_tuple * vt);
    //display the definition
    void display(std::ostream & out, def * d );
public:
    //check the quantifier
    lbool check(model_constructor * mct, quantifier * q, expr_ref_buffer & instantiations, expr_ref_buffer & instantiations_star, bool mk_inst_star);
    //exhaustive instantiate
    lbool exhaustive_instantiate(model_constructor * mct, quantifier * q, bool use_rel_domain, expr_ref_buffer & instantiations);


protected:
    eval_node * mk_eval_node(expr * e, ptr_vector<eval_node> & active, ptr_buffer<eval_node> & vars, obj_map< expr, eval_node *> & evals, expr * parent = 0);

    lbool do_eval_check(model_constructor * mct, quantifier * q, ptr_vector<eval_node> & active, ptr_buffer<eval_node> & vars, 
                        ptr_buffer<val> & vsub, expr_ref_buffer & instantiations, unsigned var_bind_count, bool & repaired);
    //lbool do_eval_check(model_constructor * mct, quantifier * q, ptr_vector<eval_node> & active, ptr_buffer<eval_node> & vars, 
    //                    cond * curr_cond, expr_ref_buffer & instantiations, unsigned var_bind_count, bool & repaired);
public:
    //eval check
    lbool eval_check(model_constructor * mct, quantifier * q, expr_ref_buffer & instantiations, bool & repaired);
};

}

#endif
