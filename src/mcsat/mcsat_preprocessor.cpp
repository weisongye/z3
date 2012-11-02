/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_preprocessor.cpp

Abstract:

    MCSAT preprocessor based on assertion stacks

Author:

    Leonardo de Moura (leonardo) 2012-11-01.

Revision History:

--*/
#include"mcsat_preprocessor.h"
#include"assertion_stack.h"
#include"tactic.h"

namespace mcsat {

    struct preprocessor::imp {
        assertion_stack     m_stack;
        sref_vector<tactic>  m_before_tactics;
        sref_vector<tactic>  m_after_tactics;
        
        imp(ast_manager & m, bool proofs_enabled, bool models_enabled, bool core_enabled):
            m_stack(m, proofs_enabled, models_enabled, core_enabled) {
        }

        ast_manager & m() const { return m_stack.m(); }

        void add_before_tactic(tactic * t) {
            m_before_tactics.push_back(t);
        }

        void add_after_tactic(tactic * t) {
            m_after_tactics.push_back(t);
        }

        void apply_tactics() {
            // TODO
        }

        void commit() {
            apply_tactics();
            m_stack.commit();
        }
        
        void push() {
            apply_tactics();
            m_stack.push();
        }
        
        void pop(unsigned num_scopes) {
            m_stack.pop(num_scopes);
        }

    };

    preprocessor::preprocessor(ast_manager & m, bool proofs_enabled, bool models_enabled, bool core_enabled) {
        m_imp = alloc(imp, m, proofs_enabled, models_enabled, core_enabled);
    }

    preprocessor::~preprocessor() {
        dealloc(m_imp);
    }
    
    ast_manager & preprocessor::m() const {
        return m_imp->m();
    }

    void preprocessor::add_before_tactic(tactic * t) {
        m_imp->add_before_tactic(t);
    }
    
    void preprocessor::add_after_tactic(tactic * t) {
        m_imp->add_after_tactic(t);
    }

    void preprocessor::assert_expr(expr * f, proof * pr, expr_dependency * d) {
        m_imp->m_stack.assert_expr(f, pr, d);
    }

    void preprocessor::assert_expr(expr * f) {
        m_imp->m_stack.assert_expr(f);
    }
        
    void preprocessor::commit() {
        m_imp->commit();
    }

    void preprocessor::push() {
        m_imp->push();
    }

    void preprocessor::pop(unsigned num_scopes) {
        m_imp->pop(num_scopes);
    }
    
    unsigned preprocessor::size() const {
        return m_imp->m_stack.size();
    }

    expr * preprocessor::form(unsigned i) const {
        return m_imp->m_stack.form(i);
    }

    proof * preprocessor::pr(unsigned i) const {
        return m_imp->m_stack.pr(i);
    }

    expr_dependency * preprocessor::dep(unsigned i) const {
        return m_imp->m_stack.dep(i);
    }
    
    bool preprocessor::is_well_sorted() const {
        return m_imp->m_stack.is_well_sorted();
    }
    
    void preprocessor::convert(model_ref & m) {
        return m_imp->m_stack.convert(m);
    }

    void preprocessor::display(std::ostream & out) const {
        m_imp->m_stack.display(out, "solver");
    }

};
