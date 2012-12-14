/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    goal_num_occurs.cpp

Abstract:


Author:

    Leonardo de Moura (leonardo) 2012-10-20.

Revision History:

--*/
#include"goal_num_occurs.h"
#include"goal.h"
#include"assertion_stream.h"

void goal_num_occurs::operator()(assertion_stream const & s, bool from_qhead) {
    expr_fast_mark1   visited;
    unsigned sz = s.size();
    for (unsigned i = from_qhead ? s.qhead() : 0; i < sz; i++) {
        process(s.form(i), visited);
    }
}

void goal_num_occurs::operator()(goal const & g) {
    goal2stream s(const_cast<goal&>(g));
    operator()(s);
}
