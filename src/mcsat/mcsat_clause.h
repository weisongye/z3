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
#ifndef _MCSAT_CLAUSE_H_
#define _MCSAT_CLAUSE_H_

#include"mcsat_literal.h"
#include"approx_set.h"
#include"ast.h"

namespace mcsat {

    struct node2u {
        unsigned operator()(node n) const { return n.index(); }
    };

    typedef approx_set_tpl<node, node2u, unsigned> node_approx_set;

    class clause {
        unsigned        m_id;
        unsigned        m_size;
        node_approx_set m_approx;
        unsigned        m_used:1;
        unsigned        m_learned:1;
        unsigned        m_reinit_stack:1;
        unsigned        m_mark:1;
        proof *         m_pr;
        literal         m_lits[0];

        friend class clause_manager;
        friend class kernel;

        static size_t get_obj_size(unsigned num_lits);
        clause(unsigned id, unsigned sz, literal const * lits, bool learned, proof * pr);

        bool on_reinit_stack() const { return m_reinit_stack; }
        void set_reinit_stack(bool f) { m_reinit_stack = f; }
        void mark() { m_mark = true; }
        void reset_mark() { m_mark = false; }
        bool is_marked() const { return m_mark; }

    public:
        unsigned id() const { return m_id; }
        unsigned size() const { return m_size; }
        literal const & operator[](unsigned idx) const { SASSERT(idx < m_size); return m_lits[idx]; }
        bool is_learned() const { return m_learned; }
        node_approx_set approx() const { return m_approx; }
        bool contains(literal l) const;
        bool contains(node v) const;
        void mark_used() { m_used = true; }
        void unmark_used() { m_used = false; }
        proof * pr() const { return m_pr; }
    };
    
    class clause_manager {
        struct imp;
        imp * m_imp;
        
        friend class kernel;
        clause_manager();
        ~clause_manager();

        clause * mk_lemma(unsigned sz, literal const * lits, proof * pr);
        void push(bool user);
        void pop(unsigned num_scopes, bool user);

        typedef ptr_vector<clause>::const_iterator iterator;
        iterator begin_lemmas() const;
        iterator end_lemmas() const;
        void gc(ptr_vector<clause> const & to_delete);

    public:
        clause * mk(unsigned sz, literal const * lits, proof * pr);
    };

};

#endif
