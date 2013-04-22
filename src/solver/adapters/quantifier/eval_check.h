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

#include"model_check.h"

namespace qsolver
{

class eval_check;

class eval_node
{
    friend class eval_check;    //temporary
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
    bool can_evaluate() { return is_app(m_e) && (is_ground(m_e) || m_children_eval_count==to_app(m_e)->get_num_args()); }
};


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
                        ptr_buffer<val> & vsub, expr_ref_buffer & esub, 
                        expr_ref_buffer & instantiations, unsigned var_bind_count, bool & repaired, 
                        sbuffer<unsigned> & start_index, bool firstTime = false);
public:
    //eval check
    lbool run(mc_context & mc, model_constructor * mct, quantifier * q, expr_ref_buffer & instantiations, bool & repaired);
};

}

#endif
