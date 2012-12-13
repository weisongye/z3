/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    assertion_stream.h

Abstract:

    Abstract wrapper for assertion_stacks and goals.
    It allows us to build procedures that operate on
    both of them.

Author:

    Leonardo de Moura (leonardo) 2012-12-13

Revision History:

*/
#ifndef _ASSERTION_STREAM_H_
#define _ASSERTION_STREAM_H_

#include"ast.h"
#include"ref.h"
class assertion_stack;
class goal;
class extension_model_converter;
class filter_model_converter;

class assertion_stream {
public:
    virtual ~assertion_stream();

    virtual bool is_frozen(func_decl * f) const = 0;
    bool is_frozen(app * f) { return is_frozen(f); }
    
    virtual ast_manager & m() const = 0;
    
    virtual bool models_enabled() const = 0;
    virtual bool proofs_enabled() const = 0;
    virtual bool unsat_core_enabled() const = 0;
    virtual bool inconsistent() const = 0;

    virtual void inc_depth() = 0;
    
    virtual unsigned qhead() const = 0;
    virtual unsigned size() const = 0;
    virtual unsigned num_exprs() const = 0;
    
    virtual void assert_expr(expr * f, proof * pr, expr_dependency * d) = 0;
    virtual void assert_expr(expr * f) = 0;
    
    virtual expr * form(unsigned i) const = 0;
    virtual proof * pr(unsigned i) const = 0;
    virtual expr_dependency * dep(unsigned i) const = 0;
    virtual void update(unsigned i, expr * f, proof * pr = 0, expr_dependency * dep = 0) = 0;
    
    virtual bool is_well_sorted() const = 0;

    virtual void add_filter(func_decl * f) = 0;
    virtual void add_definition(app * c, expr * def, proof * pr, expr_dependency * dep) = 0;
    
    virtual void elim_redundancies() = 0;

    virtual void display(std::ostream & out) = 0;
};

class assertion_stack2stream : public assertion_stream {
    assertion_stack & m_stack;
public:
    assertion_stack2stream(assertion_stack & s);
    virtual ~assertion_stack2stream();

    virtual bool is_frozen(func_decl * f) const;
    
    virtual ast_manager & m() const;
    
    virtual bool models_enabled() const;
    virtual bool proofs_enabled() const;
    virtual bool unsat_core_enabled() const;
    virtual bool inconsistent() const;

    virtual void inc_depth();
    
    virtual unsigned qhead() const;
    virtual unsigned size() const;
    virtual unsigned num_exprs() const;
    
    virtual void assert_expr(expr * f, proof * pr, expr_dependency * d);
    virtual void assert_expr(expr * f);
    
    virtual expr * form(unsigned i) const;
    virtual proof * pr(unsigned i) const;
    virtual expr_dependency * dep(unsigned i) const;
    virtual void update(unsigned i, expr * f, proof * pr, expr_dependency * dep);
    
    virtual bool is_well_sorted() const;

    virtual void add_filter(func_decl * f);
    virtual void add_definition(app * c, expr * def, proof * pr, expr_dependency * dep);

    virtual void elim_redundancies();

    virtual void display(std::ostream & out);
};

class goal2stream : public assertion_stream {
protected:
    goal & m_goal;
public:
    goal2stream(goal & g);
    virtual ~goal2stream();

    virtual bool is_frozen(func_decl * f) const;

    virtual ast_manager & m() const;
    
    virtual bool models_enabled() const;
    virtual bool proofs_enabled() const;
    virtual bool unsat_core_enabled() const;
    virtual bool inconsistent() const;

    virtual void inc_depth();
    
    virtual unsigned qhead() const;
    virtual unsigned size() const;
    virtual unsigned num_exprs() const;
    
    virtual void assert_expr(expr * f, proof * pr, expr_dependency * d);
    virtual void assert_expr(expr * f);
    
    virtual expr * form(unsigned i) const;
    virtual proof * pr(unsigned i) const;
    virtual expr_dependency * dep(unsigned i) const;
    virtual void update(unsigned i, expr * f, proof * pr, expr_dependency * dep);
    
    virtual bool is_well_sorted() const;

    virtual void add_filter(func_decl * f);
    virtual void add_definition(app * c, expr * def, proof * pr, expr_dependency * dep);

    virtual void elim_redundancies();

    virtual void display(std::ostream & out);
};

class goal_and_emc2stream : public goal2stream {
    ref<extension_model_converter> m_mc;
public:
    goal_and_emc2stream(goal & g);
    virtual ~goal_and_emc2stream();
    virtual void add_definition(app * c, expr * def, proof * pr, expr_dependency * dep);
    extension_model_converter * mc() const { return m_mc.get(); }
};

class goal_and_fmc2stream : public goal2stream {
    ref<filter_model_converter> m_mc;
public:
    goal_and_fmc2stream(goal & g);
    virtual ~goal_and_fmc2stream();
    virtual void add_filter(func_decl * f);
    filter_model_converter * mc() const { return m_mc.get(); }
};

class stream_report {
    struct imp;
    imp * m_imp;
public:
    stream_report(char const * id, assertion_stream & s);
    ~stream_report();
};

#endif
