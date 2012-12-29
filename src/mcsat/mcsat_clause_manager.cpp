/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_clause_manager.cpp

Abstract:

    MCSAT clause manager

Author:

    Leonardo de Moura (leonardo) 2012-12-28.

Revision History:

--*/
#include"mcsat_clause_manager.h"
#include"small_object_allocator.h"

namespace mcsat {

    struct clause_manager::imp {
        region                 m_region;    // for main and auxiliary clauses.
        small_object_allocator m_allocator; // for lemmas.
        id_gen                 m_id_gen;
        ptr_vector<clause>     m_clauses;
        ptr_vector<clause>     m_lemmas;
        unsigned_vector        m_base_scopes; 
        unsigned_vector        m_scopes;
        imp():
            m_allocator("mcsat_clause_manager") {}

        void del_lemma(clause * c) {
            m_id_gen.recycle(c->id());
            size_t obj_sz = clause::get_obj_size(c->size());
            c->~clause();
            m_allocator.deallocate(obj_sz, c);
        }

        void del_clause(clause * c) {
            m_id_gen.recycle(c->id());
            c->~clause();
        }

        clause * mk(unsigned sz, literal const * lits, clause::kind k, proof * pr) {
            unsigned id = m_id_gen.mk();
            size_t obj_sz = clause::get_obj_size(sz);
            void * mem;
            if (k == clause::LEMMA)
                mem = m_allocator.allocate(obj_sz);
            else
                mem = m_region.allocate(obj_sz);
            clause * cls = new (mem) clause(id, sz, lits, k, pr);
            if (k == clause::LEMMA)
                m_lemmas.push_back(cls);
            else
                m_clauses.push_back(cls);
            return cls;
        }

        void push(bool user) {
            SASSERT(user || m_scopes.size() == m_base_scopes.size());
            SASSERT(m_scopes.size() >= m_base_scopes.size());
            m_scopes.push_back(m_clauses.size());
            if (user)
                m_base_scopes.push_back(m_lemmas.size());
        }
        
        void restore_clauses(unsigned old_sz) {
            unsigned sz = m_clauses.size();
            SASSERT(old_sz <= sz);
            for (unsigned i = old_sz; i < sz; i++) {
                clause * c = m_clauses[i];
                del_clause(c);
            }
            m_clauses.shrink(old_sz);
        }

        void restore_lemmas(unsigned old_sz) {
            unsigned sz = m_lemmas.size();
            SASSERT(old_sz <= sz);
            for (unsigned i = old_sz; i < sz; i++) {
                clause * c = m_lemmas[i];
                del_lemma(c);
            }
            m_lemmas.shrink(old_sz);
        }
        
        void pop(unsigned num_scopes, bool user) {
            SASSERT(user || m_scopes.size() == m_base_scopes.size());
            SASSERT(m_scopes.size() >= m_base_scopes.size());
            SASSERT(num_scopes <= m_scopes.size());
            unsigned new_lvl    = m_scopes.size() - num_scopes;
            unsigned old_sz     = m_scopes[new_lvl];
            restore_clauses(old_sz);
            m_scopes.shrink(new_lvl);
            if (user) {
                SASSERT(num_scopes <= m_base_scopes.size());
                unsigned new_lvl    = m_base_scopes.size() - num_scopes;
                unsigned old_sz     = m_base_scopes[new_lvl];
                restore_lemmas(old_sz);
                m_base_scopes.shrink(new_lvl);
            }
        }
    };

    clause_manager::clause_manager() {
        m_imp = alloc(imp);
    }

    clause_manager::~clause_manager() {
        dealloc(m_imp);
    }
    
    void clause_manager::push(bool user) {
        m_imp->push(user);
    }

    void clause_manager::pop(unsigned num_scopes, bool user) {
        m_imp->pop(num_scopes, user);
    }

    clause * clause_manager::mk(unsigned sz, literal const * lits, proof * pr) {
        return m_imp->mk(sz, lits, clause::MAIN, pr);
    }

    clause * clause_manager::mk_aux(unsigned sz, literal const * lits, proof * pr) {
        return m_imp->mk(sz, lits, clause::AUX, pr);
    }

    clause * clause_manager::mk_lemma(unsigned sz, literal const * lits, proof * pr) {
        return m_imp->mk(sz, lits, clause::LEMMA, pr);
    }

    clause_manager::iterator clause_manager::begin_lemmas() const {
        unsigned begin = m_imp->m_base_scopes.empty() ? 0 : m_imp->m_base_scopes.back();
        return m_imp->m_lemmas.begin() + begin;
    }

    clause_manager::iterator clause_manager::end_lemmas() const {
        return m_imp->m_lemmas.end();
    }

    void clause_manager::gc(ptr_vector<clause> const & to_delete) {
        DEBUG_CODE({
                iterator it  = begin_lemmas();
                iterator end = end_lemmas();
                for (; it != end; ++it) {
                    SASSERT(!(*it)->is_marked());
                }
            });

        iterator it  = to_delete.begin();
        iterator end = to_delete.end();
        for (; it != end; ++it) {
            SASSERT(!(*it)->is_marked());
            (*it)->mark();
        }
        
        DEBUG_CODE({
                unsigned num_marked = 0;
                iterator it  = begin_lemmas();
                iterator end = end_lemmas();
                for (; it != end; ++it) {
                    if ((*it)->is_marked())
                        num_marked++;
                }
                SASSERT(to_delete.size() == num_marked);
            });

        unsigned _begin = m_imp->m_base_scopes.empty() ? 0 : m_imp->m_base_scopes.back();
        unsigned _end   = m_imp->m_lemmas.size();
        SASSERT(_begin <= _end);
        unsigned j     = _begin;
        for (unsigned i = _begin; i < _end; i++) {
            clause * c = m_imp->m_lemmas[i];
            SASSERT(c->is_lemma());
            if (c->is_marked()) {
                c->reset_mark();
                m_imp->del_lemma(c);
            }
            else {
                m_imp->m_lemmas[j] = c;
                j++;
            }
        }
        m_imp->m_lemmas.shrink(j);
    }

    clause_manager::iterator clause_manager::begin_clauses() const {
        unsigned begin = m_imp->m_scopes.empty() ? 0 : m_imp->m_scopes.back();
        return m_imp->m_clauses.begin() + begin;
    }

    clause_manager::iterator clause_manager::end_clauses() const {
        return m_imp->m_clauses.end();
    }

};
