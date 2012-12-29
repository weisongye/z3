/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_clause_manager.h

Abstract:

    MCSAT clause

Author:

    Leonardo de Moura (leonardo) 2012-12-28.

Revision History:

--*/
#ifndef _MCSAT_CLAUSE_MANAGER_H_
#define _MCSAT_CLAUSE_MANAGER_H_

#include"mcsat_clause.h"

namespace mcsat {

    class clause_manager {
        struct imp;
        imp * m_imp;
    public:
        typedef ptr_vector<clause>::const_iterator iterator;

        clause_manager();
        ~clause_manager();

        clause * mk(unsigned sz, literal const * lits, proof * pr);
        clause * mk_aux(unsigned sz, literal const * lits, proof * pr);
        clause * mk_lemma(unsigned sz, literal const * lits, proof * pr);

        // Remark: lemmas are part of user defined scope_levels.
        
        void push(bool user);
        void pop(unsigned num_scopes, bool user);
        
        // Remark: the following iterators only traverse
        // the clauses in the current scope levels

        iterator begin_lemmas() const;
        iterator end_lemmas() const;
        void gc(ptr_vector<clause> const & to_delete);
        
        iterator begin_clauses() const;
        iterator end_clauses() const;
    };

};

#endif
