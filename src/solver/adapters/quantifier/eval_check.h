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
class model_constructor;

//term condition (tuple of terms)
class annot_entry {
    friend class mc_context;
    friend class eval_check;
protected:
    //the data
    unsigned m_size;
    expr * m_result;
    expr * m_vec[];
    annot_entry(unsigned sz) : m_size(sz) {}
    static annot_entry * mk(mc_context & mc, unsigned arity);
public:
    //get the size of the condition
    unsigned get_size() { return m_size; }
    //get the value at index
    expr * get_value(unsigned i) { return m_vec[i]; }
    //get annotation at index
    expr * get_annotation(unsigned i) { return m_vec[m_size + i]; }
    //get result
    expr * get_result() { return m_result; }
    //is value
    bool is_value();
};


//trie of values
class annot_entry_trie 
{
private:
    unsigned m_data;
    obj_map< expr, annot_entry_trie  * > m_children;
    bool add(mc_context & mc, annot_entry * c, unsigned index, unsigned data_val);
    bool evaluate(annot_entry * c, unsigned index, unsigned & data_val);
    bool evaluate(expr_ref_buffer & vals, unsigned index, unsigned & data_val);
public:
    annot_entry_trie () : m_data(0) {}
    bool add(mc_context & mc, annot_entry * c, unsigned data_val) { return add(mc, c, 0, data_val); }
    bool evaluate(annot_entry * c, unsigned & data_val) { return evaluate(c, 0, data_val); }
    bool evaluate(expr_ref_buffer & vals, unsigned & data_val) { return evaluate(vals, 0, data_val); }
};


/*
class add_inst 
{
public:

};
*/

class simple_def
{
    friend class eval_check;
    friend class model_constructor;
protected:
    annot_entry_trie m_tct;
    ptr_vector<annot_entry> m_conds;
    ptr_vector<annot_entry> m_unsorted_conds;
    ptr_vector<annot_entry> m_unsorted_repair_conds;
    expr * m_else;
    bool m_sorted;
    void sort_entries();
    bool get_index_of(annot_entry * c, unsigned & index);
public:
    simple_def() : m_else(0), m_sorted(true) {}
    unsigned get_num_entries() { return m_unsorted_conds.size(); }
    annot_entry * get_condition(unsigned i) { return m_unsorted_conds[i]; }
    expr * get_value(unsigned i) { return m_unsorted_conds[i]->get_result(); }
    void set_else(expr * ee) {m_else = ee; }
    expr * get_else() { return m_else; }
    //evaluate
    expr * evaluate(annot_entry * c, bool partial = false);
    expr * evaluate(expr_ref_buffer & vals, bool partial = false);
    annot_entry * get_entry(expr_ref_buffer & vals);
    //is this a repair entry?
    unsigned get_num_repair_entries() { return m_unsorted_repair_conds.size(); }
    bool is_repair_entry(annot_entry * c);
    //add entry to the definition
    bool append_entry(mc_context & mc, annot_entry * c, bool is_repair = false);
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
    unsigned m_q_depth; //depth in quantifier
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
    void notify_value(expr * ev);
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
    // only follow partial evaluation
    bool m_ground_partial_evaluation;
protected: //temporary information
    //first time
    bool m_first_time;
    //start indicies
    sbuffer<unsigned> m_start_index;
    //start score
    unsigned m_start_score;
    //temporary
    unsigned m_depth;
    //map from variables to the evaluation nodes that bind them
    u_map< ptr_vector< eval_node > > m_bind_terms;
    //variable eval nodes
    ptr_vector<eval_node> m_vars;
    //variable bound count
    unsigned m_var_bind_count;
    //store the number of entries for each function we process
    obj_map< func_decl, unsigned > m_func_num_real_entries;
    obj_map< func_decl, unsigned > m_func_num_entries;
    //process repair entries
    bool m_process_repair_entries;
protected:
    void set_var_bind_eval_node(eval_node * en, unsigned vid);
    void set_var_bound(unsigned vid, ptr_vector<eval_node> & new_active);
    void set_var_unbound(unsigned vid);
public:
    eval_check(ast_manager & _m);
protected:
    eval_node * mk_eval_node(mc_context & mc, model_constructor * mct, expr * e, ptr_vector<eval_node> & active, obj_map< expr, eval_node *> & evals, unsigned q_depth = 0);

    lbool do_eval_check(mc_context & mc, model_constructor * mct, quantifier * q, ptr_vector<eval_node> & active, 
                        expr_ref_buffer & vsub, expr_ref_buffer & esub, expr_ref_buffer & instantiations);
public:
    //eval check
    lbool run(mc_context & mc, model_constructor * mct, quantifier * q, expr_ref_buffer & instantiations);
};

}

#endif
