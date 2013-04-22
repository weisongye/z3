/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    eval_check.h

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-04-21.

--*/

#ifndef _EVAL_CHECK_H_
#define _EVAL_CHECK_H_

#include"ast.h"
#include"lbool.h"

namespace qsolver
{

class eval_check;
class mc_context;

//term condition (tuple of terms)
class term_cond {
    friend class mc_context;
    friend class eval_check;
protected:
    //the data
    unsigned m_size;
    expr * m_vec[];
    term_cond(unsigned sz) : m_size(sz) {}
    static term_cond * mk(mc_context & mc, unsigned arity);
public:
    //get the size of the condition
    unsigned get_size() { return m_size; }
    //get the value at index
    expr * get_value(unsigned i) { return m_vec[i]; }
    //is value
    bool is_value();
};


//trie of values
class term_cond_trie 
{
private:
    unsigned m_data;
    obj_map< expr, term_cond_trie  * > m_children;
    bool add(mc_context & mc, term_cond * c, unsigned index, unsigned data_val);
    bool evaluate(mc_context & mc, term_cond * c, unsigned index, unsigned & data_val);
    bool evaluate(mc_context & mc, expr_ref_buffer & vals, unsigned index, unsigned & data_val);
public:
    term_cond_trie () : m_data(0) {}
    bool add(mc_context & mc, term_cond * c, unsigned data_val) { return add(mc, c, 0, data_val); }
    bool evaluate(mc_context & mc, term_cond * c, unsigned & data_val) { return evaluate(mc, c, 0, data_val); }
    bool evaluate(mc_context & mc, expr_ref_buffer & vals, unsigned & data_val) { return evaluate(mc, vals, 0, data_val); }
};


class annotated_simple_def
{
    friend class eval_check;
protected:
    term_cond_trie m_tct;
    ptr_vector<term_cond> m_conds;
    ptr_vector<expr> m_values;
    ptr_vector<term_cond> m_annotations;
    expr * m_else;
public:
    annotated_simple_def() : m_else(0) {}
    unsigned get_num_entries() { return m_conds.size(); }
    term_cond * get_condition(unsigned i) { return m_conds[i]; }
    term_cond * get_annotation(unsigned i) { return m_annotations[i]; }
    expr * get_value(unsigned i) { return m_values[i]; }
    void set_else(expr * ee) {m_else = ee; }
    expr * get_else() { return m_else; }
    //evaluate
    expr * evaluate(mc_context & mc, expr_ref_buffer & vals, bool ignore_else = false);
    //add entry to the definition
    bool append_entry(mc_context & mc, term_cond * c, term_cond * a, expr * v);
};



class eval_node
{
    friend class eval_check;    //temporary
private:
    expr * m_e;
    expr * m_value;
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
    expr * get_evaluation() { return m_value; }
    bool can_evaluate() { return is_app(m_e) && (is_ground(m_e) || m_children_eval_count==to_app(m_e)->get_num_args()); }
};

class model_constructor;

class eval_check
{
protected:
    //manager
    ast_manager & m_m;
    // do instantiation limiting
    bool m_eval_check_inst_limited;
    // repeat eval check on multiple patterns
    bool m_eval_check_multiple_patterns;
public:
    eval_check(ast_manager & _m);
protected:
    eval_node * mk_eval_node(mc_context & mc, expr * e, ptr_vector<eval_node> & active, ptr_buffer<eval_node> & vars, obj_map< expr, eval_node *> & evals, expr * parent = 0);

    lbool do_eval_check(mc_context & mc, model_constructor * mct, quantifier * q, ptr_vector<eval_node> & active, ptr_buffer<eval_node> & vars, 
                        expr_ref_buffer & vsub, expr_ref_buffer & esub, 
                        expr_ref_buffer & instantiations, unsigned var_bind_count, bool & repaired, 
                        sbuffer<unsigned> & start_index, bool firstTime = false);
public:
    //eval check
    lbool run(mc_context & mc, model_constructor * mct, quantifier * q, expr_ref_buffer & instantiations, bool & repaired);
};

}

#endif
