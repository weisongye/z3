/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    model2assignment.cpp

Abstract:

    Functor for converting a pair (Model, Formula) into a set of entries t->v,
    where t is a ground expression and v is a value.

Author:

    Leonardo de Moura (leonardo) 2013-04-09.

Revision History:

--*/
#include"model2assignment.h"
#include"dec_ref_util.h"
#include"model_evaluator.h"
#include"lbool.h"
#include"for_each_expr.h"
#include"ast_pp.h"
#include"common_msgs.h"
#include"cooperate.h"

struct model2assignment::imp {
    model &                          m_model;
    expr_substitution &              m_result;
    model_evaluator                  m_eval;
    obj_map<app, lbool>              m_formula2value;
    app_ref_vector                   m_formulas;
    expr_mark                        m_eval_visited;
    expr_mark                        m_collect_u_visited;
    expr_mark                        m_collect_i_visited;
    svector<std::pair<app *, bool> > m_todo;
    volatile bool                    m_cancel;

    imp(model & m, expr_substitution & r):
        m_model(m), 
        m_result(r),
        m_eval(m),
        m_formulas(m.get_manager()) {
        m_cancel = false;
    }

    ast_manager & m() { return m_model.get_manager(); }

    void set_cancel(bool f) {
        m_cancel = f;
        m_eval.set_cancel(f);
    }

    void checkpoint() {
        if (m_cancel)
            throw exception(Z3_CANCELED_MSG);
        cooperate("model2assignment");
    }
    
    bool is_marked(app * f, bool u_context) {
        return u_context ? m_collect_u_visited.is_marked(f) : m_collect_i_visited.is_marked(f);
    }

    // Mark a formula f during collection.
    // u_context == true if the formula is in the context of a uninterpreted symbol.
    void mark(app * f, bool u_context) {
        if (is_uninterp(f)) 
            u_context = true;
        if (u_context) {
            if (f->get_num_args() > 0 || is_uninterp_const(f)) {
                if (!m_collect_u_visited.is_marked(f)) {
                    m_collect_u_visited.mark(f);
                    m_todo.push_back(std::make_pair(f, true));
                    expr_ref r(m());
                    m_eval(f, r);
                    m_result.insert(f, r);
                }
            }
        }
        else {
            if (!m_collect_i_visited.is_marked(f)) {
                m_collect_i_visited.mark(f);
                m_todo.push_back(std::make_pair(f, false));
            }
        }
    }

    lbool get_bool_value(app * f) {
        SASSERT(m().is_bool(f));
        lbool r;
        if (m_formula2value.find(f, r))
            return r;
        expr_ref val(m());
        m_eval(f, val);        
        lbool v;
        if (m().is_true(val))
            v = l_true;
        else if (m().is_false(val))
            v = l_false;
        else
            v = l_undef;
        m_formulas.push_back(f);
        m_formula2value.insert(f, v);
        return v;
    }

    void process_ite(app * f, bool u_context) {
        SASSERT(m().is_ite(f));
        app * c = to_app(f->get_arg(0));
        mark(c, u_context);
        switch (get_bool_value(c)) {
        case l_true:
            mark(to_app(f->get_arg(1)), u_context); 
            break;
        case l_false:
            mark(to_app(f->get_arg(2)), u_context); 
            break;
        default:
            mark(to_app(f->get_arg(1)), u_context); 
            mark(to_app(f->get_arg(2)), u_context); 
            break;
        }
    }

    void process_app(app * f, bool u_context) {
        if (is_uninterp(f))
            u_context = true;
        unsigned num = f->get_num_args();
        for (unsigned i = 0; i < num; i++) {
            mark(to_app(f->get_arg(i)), u_context);
        }
    }

    // Return true if c1 is a "better" formula than c2
    bool is_better(expr * c1, expr * c2) {
        return false;
    }

    void process_and(app * f, bool u_context) {
        SASSERT(m().is_and(f));
        lbool f_value = get_bool_value(f);
        if (f_value == l_undef || f_value == l_true) {
            process_app(f, u_context); // we have to consider all children
        }
        else {
            unsigned num      = f->get_num_args();
            app * false_child = 0;
            for (unsigned i = 0; i < num; i++) {
                app * c = to_app(f->get_arg(i));
                if (get_bool_value(c) == l_false) {
                    if (is_marked(c, u_context))
                        return; // And is already justified
                    if (false_child == 0 || is_better(c, false_child))
                        false_child = c;
                }
            }
            SASSERT(false_child);
            mark(false_child, u_context);
        }
    }

    void process_or(app * f, bool u_context) {
        SASSERT(m().is_or(f));
        lbool f_value = get_bool_value(f);
        if (f_value == l_undef || f_value == l_false) {
            process_app(f, u_context); // we have to consider all children
        }
        else {
            unsigned num      = f->get_num_args();
            app * true_child = 0;
            for (unsigned i = 0; i < num; i++) {
                app * c = to_app(f->get_arg(i));
                if (get_bool_value(c) == l_true) {
                    if (is_marked(c, u_context))
                        return; // And is already justified
                    if (true_child == 0 || is_better(c, true_child))
                        true_child = c;
                }
            }
            SASSERT(true_child);
            mark(true_child, u_context);
        }
    }

    // Collect relevant terms
    void collect(app * f) {
        m_todo.reset();
        mark(f, false);
        while (!m_todo.empty()) {
            checkpoint();
            app * f         = m_todo.back().first;
            bool  u_context = m_todo.back().second;
            m_todo.pop_back();
            if (f->get_family_id() == m().get_basic_family_id()) {
                switch (f->get_decl_kind()) {
                case OP_OR:
                    process_or(f, u_context); 
                    break;
                case OP_AND:
                    process_and(f, u_context);
                    break;
                case OP_ITE:
                    process_ite(f, u_context);
                    break;
                default:
                    process_app(f, u_context);
                    break;
                }
            }
            else {
                process_app(f, u_context);
            }
        }
    }

    void process(app * f) {
        collect(f);
        if (get_bool_value(f) != l_true)
            throw exception("Failed to evaluate model.");
    }
};

model2assignment::model2assignment(model & m, expr_substitution & r) {
    m_imp = alloc(imp, m, r);
}

model2assignment::~model2assignment() {
    dealloc(m_imp);
}

void model2assignment::set_cancel(bool f) {
    m_imp->set_cancel(f);
}

void model2assignment::operator()(expr * f) {
    SASSERT(is_ground(f));
    m_imp->process(to_app(f));
}

void model2assignment::operator()(unsigned n, expr * const * fs) {
    for (unsigned i = 0; i < n; i++)
        operator()(fs[i]);
}

expr_substitution & model2assignment::get_result() {
    return m_imp->m_result;
}

