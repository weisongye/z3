/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    expr_bound_propagator.h

Abstract:

    Wrapper for bound_propagator class.
    It allows us to process bounds of Z3 expression objects.

Author:

    Leonardo de Moura (leonardo) 2013-02-01.

Revision History:

--*/
#ifndef _EXPR_BOUND_PROPAGATOR_H_
#define _EXPR_BOUND_PROPAGATOR_H_

#include"ast.h"
#include"params.h"

class statistics;

class expr_bound_propagator {
    struct imp;
    imp * m_imp;
public:
    typedef unsynch_mpq_manager numeral_manager;

    expr_bound_propagator(ast_manager & m, params_ref const & p = params_ref());
    ~expr_bound_propagator();

    numeral_manager & nm() const;

    void updt_params(params_ref const & p);
    static void get_param_descrs(param_descrs & r);

    void collect_statistics(statistics & st) const;
    void reset_statistics();

    /**
       \brief Assert t into the bound propagator.
       Return true if t can be processed by the propagator, and false otherwise
    */
    bool assert_expr(expr * t);
    
    bool has_lower(expr * t) const;
    bool has_upper(expr * t) const;
    bool lower(expr * x, mpq & k, bool & strict) const;
    bool upper(expr * x, mpq & k, bool & strict) const;
    /**
       \brief Return true if p is a polynomial of the form a_1*x_1 + ... + a_n*x_n, and has a lower bound based on the bounds for the x_i's.
       Return false otherwise.
       The bound is stored in k and strict.
    */
    bool poly_lower(expr * p, mpq & k, bool & strict);
    /**
       \brief Return true if p is a polynomial of the form a_1*x_1 + ... + a_n*x_n, and has a upper bound based on the bounds for the x_i's.
       Return false otherwise.
       The bound is stored in k and strict.
    */
    bool poly_upper(expr * p, mpq & k, bool & strict);
    void propagate();
    bool inconsistent() const;
    void reset();
    void push();
    void pop(unsigned num_scopes);
    void set_cancel(bool f);
    
    unsigned num_exprs() const;
    /**
       \brief Return the i-th expression in the propagator.
       \pref i < num_exprs()
    */
    expr * get_expr(unsigned i) const;
    void display(std::ostream & out) const;
};

#endif
