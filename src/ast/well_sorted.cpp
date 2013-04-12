/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    well_sorted.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-12-29.

Revision History:

--*/

#include<sstream>
#include"for_each_expr.h"
#include"well_sorted.h"
#include"ast_ll_pp.h"
#include"ast_pp.h"
#include"warning.h"
#include"ast_smt2_pp.h"
#include"expr_delta_pair.h"
#include"hashtable.h"

struct well_sorted_proc {
    ast_manager & m_manager;
    bool          m_error;
    
    well_sorted_proc(ast_manager & m):m_manager(m), m_error(false) {}

    void check_q_vars(quantifier * q) {
        unsigned num_decls = q->get_num_decls();
        hashtable<expr_delta_pair, obj_hash<expr_delta_pair>, default_eq<expr_delta_pair> > cache;
        svector<expr_delta_pair> todo;
        todo.push_back(expr_delta_pair(q->get_expr(), 0));
        while (!todo.empty()) {
            expr_delta_pair e = todo.back();
            todo.pop_back();
            if (is_app(e.m_node)) {
                unsigned num_args = to_app(e.m_node)->get_num_args();
                for (unsigned i = 0; i < num_args; i++) {
                    expr * c = to_app(e.m_node)->get_arg(i);
                    expr_delta_pair new_e(c, e.m_delta);
                    if (!cache.contains(new_e)) {
                        cache.insert(new_e);
                        todo.push_back(new_e);
                    }
                }
            }
            else if (is_quantifier(e.m_node)) {
                unsigned new_delta = e.m_delta + to_quantifier(e.m_node)->get_num_decls();
                unsigned num_children = to_quantifier(e.m_node)->get_num_children();
                for (unsigned i = 0; i < num_children; i++) {
                    expr * c = to_quantifier(e.m_node)->get_child(i);
                    expr_delta_pair new_e(c, new_delta);
                    if (!cache.contains(new_e)) {
                        cache.insert(new_e);
                        todo.push_back(new_e);
                    }
                }
            }
            else {
                SASSERT(is_var(e.m_node));
                var * x = to_var(e.m_node);
                unsigned x_idx = x->get_idx();
                if (x_idx >= e.m_delta && x_idx - e.m_delta < num_decls) {
                    // x is q variable
                    sort * expected_sort = q->get_decl_sort(num_decls - (x_idx - e.m_delta) - 1);
                    sort * actual_sort   = x->get_sort();
                    if (actual_sort != expected_sort) {
                        std::ostringstream strm;
                        strm << "Invalid variable occurrence, sort does not match sort in the quantifier.\n";
                        strm << "Expected sort: " << mk_pp(expected_sort, m_manager) << "\n";
                        strm << "Actual sort:   " << mk_pp(actual_sort, m_manager) << "\n";
                        strm << "Quantifier:\n"   << mk_pp(q, m_manager) << "\n";
                        strm << "Variable:      " << mk_pp(x, m_manager) << ", delta: " << e.m_delta << "\n";
                        warning_msg(strm.str().c_str());
                        m_error = true;
                    }
                }
            }
        }
    }
    
    void operator()(var * v) {}

    void operator()(quantifier * n) {
        expr const * e  = n->get_expr();
        check_q_vars(n);
        if (!m_manager.is_bool(e)) {
            warning_msg("quantifier's body must be a boolean.");
            m_error = true;
        }
    }

    void operator()(app * n) {   
        unsigned num_args  = n->get_num_args();
        func_decl * decl   = n->get_decl();
        if (num_args != decl->get_arity() && !decl->is_associative()) {
            TRACE("ws", tout << "unexpected number of arguments.\n" << mk_ismt2_pp(n, m_manager););
            warning_msg("unexpected number of arguments.");
            m_error = true;
            return;
        }

        for (unsigned i = 0; i < num_args; i++) {
            sort * actual_sort   = m_manager.get_sort(n->get_arg(i));
            sort * expected_sort = decl->is_associative() ? decl->get_domain(0) : decl->get_domain(i);
            if (expected_sort != actual_sort) {
                TRACE("tc", tout << "sort mismatch on argument #" << i << ".\n" << mk_ismt2_pp(n, m_manager);
                      tout << "Sort mismatch for argument " << i+1 << " of " << mk_ismt2_pp(n, m_manager, false) << "\n";
                      tout << "Expected sort: " << mk_pp(expected_sort, m_manager) << "\n";
                      tout << "Actual sort:   " << mk_pp(actual_sort, m_manager) << "\n";
                      tout << "Function sort: " << mk_pp(decl, m_manager) << ".";
                      );
                std::ostringstream strm;
                strm << "Sort mismatch for argument " << i+1 << " of " << mk_ll_pp(n, m_manager, false) << "\n";
                strm << "Expected sort: " << mk_pp(expected_sort, m_manager) << "\n";
                strm << "Actual sort:   " << mk_pp(actual_sort, m_manager) << "\n";
                strm << "Function sort: " << mk_pp(decl, m_manager) << ".";
                warning_msg(strm.str().c_str());
                m_error = true;
                return;
            }
        }
    }
};

bool is_well_sorted(ast_manager const & m, expr * n) {
    well_sorted_proc p(const_cast<ast_manager&>(m));
    for_each_expr(p, n);
    return !p.m_error;
}


