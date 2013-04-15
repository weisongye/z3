/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    model2assignment.h

Abstract:

    Functor for converting a pair (Model, Formula) into a set of entries t->v,
    where t is a ground expression and v is a value.

Author:

    Leonardo de Moura (leonardo) 2013-04-09.

Revision History:

--*/
#ifndef _MODEL2ASSIGNMENT_H_
#define _MODEL2ASSIGNMENT_H_

#include"model.h"
#include"expr_substitution.h"
#include"z3_exception.h"

class model2assignment {
    struct imp;
    imp * m_imp;
public:
    typedef default_exception exception;

    model2assignment(model & m, expr_substitution & result);
    ~model2assignment();
    /**
       \brief Add more entries to the mapping result. After executing this method,
       result must containt enough entries to justify that f is true.
       
       \pre f is satisfied by the model provided in the constructor.
    */
    void operator()(expr * f, bool assertion=true);
    void operator()(unsigned n, expr * const * fs, bool assertion=true);
    /**
       \brief Return a reference to the object provided in the constructor.
    */
    expr_substitution & get_result();

    void set_cancel(bool f);
};

#endif
