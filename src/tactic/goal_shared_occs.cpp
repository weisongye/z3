/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    goal_shared_occs.cpp

Abstract:

    Functor for computing the set of shared occurrences in a goal.

Author:

    Leonardo de Moura (leonardo) 2011-12-28

Revision History:

--*/
#include"goal_shared_occs.h"
#include"assertion_stream.h"

void goal_shared_occs::operator()(assertion_stream const & g, bool from_qhead) {
    m_occs.reset();
    shared_occs_mark visited;
    unsigned sz = g.size();
    for (unsigned i = from_qhead ? g.qhead() : 0; i < sz; i++) {
        expr * t = g.form(i);
        m_occs(t, visited);
    }
}

void goal_shared_occs::operator()(goal const & g) {
    goal2stream s(const_cast<goal&>(g));
    (*this)(s);
}
