/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_clause.h

Abstract:

    MCSAT clause

Author:

    Leonardo de Moura (leonardo) 2012-12-27.

Revision History:

--*/
#include"mcsat_clause.h"

namespace mcsat {

    static node_approx_set mk_approx(unsigned num, literal const * lits) {
        node_approx_set r;
        for (unsigned i = 0; i < num; i++) 
            r.insert(lits[i].var());
        return r;
    }

    size_t clause::get_obj_size(unsigned num_lits) { 
        return sizeof(clause) + num_lits * sizeof(literal); 
    }

    clause::clause(unsigned id, unsigned sz, literal const * lits, bool learned, proof * pr):
        m_id(id),
        m_size(sz),
        m_approx(mk_approx(sz, lits)),
        m_used(false),
        m_learned(learned),
        m_reinit_stack(false),
        m_mark(false),
        m_pr(pr) {
        for (unsigned i = 0; i < sz; i++)
            m_lits[i] = lits[i];
    }

    bool clause::contains(literal l) const {
        for (unsigned i = 0; i < size(); i++)
            if (m_lits[i] == l)
                return true;
        return false;
    }

    bool clause::contains(node v) const {
        for (unsigned i = 0; i < size(); i++)
            if (m_lits[i].var() == v)
                return true;
        return false;
    }

};
