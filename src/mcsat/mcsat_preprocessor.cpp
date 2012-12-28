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
        assertion_stack      m_stack;
        tactic_ref_vector    m_before_tactics;
        tactic_ref_vector    m_after_tactics;
        
        imp(ast_manager & m, bool proofs_enabled, bool models_enabled, bool core_enabled):
            m_stack(m, proofs_enabled, models_enabled, core_enabled) {
        }

        ast_manager & m() const { return m_stack.m(); }

        void add_tactic_before(tactic * t) {
            m_before_tactics.push_back(t);
        }

        void add_tactic_after(tactic * t) {
            m_after_tactics.push_back(t);
        }

        void apply_tactics() {
            unsigned i = m_before_tactics.size();
            while (i > 0) {
                --i;
                (*m_before_tactics[i])(m_stack);
            }

            for (unsigned i = 0; i < m_after_tactics.size(); i++) {
                (*m_after_tactics[i])(m_stack);
            }
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

        unsigned scope_lvl() const {
            return m_stack.scope_lvl();
        }

        static void set_cancel(sref_vector<tactic> & ts, bool f) {
            for (unsigned i = 0; i < ts.size(); i++) {
                ts[i]->set_cancel(f);
            }
        }
        
        void set_cancel(bool f) {
            set_cancel(m_before_tactics, f);
            set_cancel(m_after_tactics, f);
        }
    };

    preprocessor::preprocessor(ast_manager & m, bool proofs_enabled, bool models_enabled, bool core_enabled) {
        m_imp = alloc(imp, m, proofs_enabled, models_enabled, core_enabled);
    }

    preprocessor::~preprocessor() {
        dealloc(m_imp);
    }

    bool preprocessor::models_enabled() const { 
        return m_imp->m_stack.models_enabled(); 
    }

    bool preprocessor::proofs_enabled() const { 
        return m_imp->m_stack.proofs_enabled(); 
    }

    bool preprocessor::unsat_core_enabled() const { 
        return m_imp->m_stack.unsat_core_enabled(); 
    }
    
    ast_manager & preprocessor::m() const {
        return m_imp->m();
    }

    void preprocessor::add_tactic_before(tactic * t) {
        m_imp->add_tactic_before(t);
    }
    
    void preprocessor::add_tactic_after(tactic * t) {
        m_imp->add_tactic_after(t);
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

    unsigned preprocessor::scope_lvl() const {
        return m_imp->scope_lvl();
    }
    
    unsigned preprocessor::size() const {
        return m_imp->m_stack.size();
    }

    unsigned preprocessor::qhead() const {
        return m_imp->m_stack.qhead();
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

    bool preprocessor::inconsistent() const {
        return m_imp->m_stack.inconsistent();
    }
    
    bool preprocessor::is_well_sorted() const {
        return m_imp->m_stack.is_well_sorted();
    }

    void preprocessor::freeze(func_decl * f) {
        m_imp->m_stack.freeze(f);
    }

    bool preprocessor::is_frozen(func_decl * f) const {
        return m_imp->m_stack.is_frozen(f);
    }

    bool preprocessor::is_eliminated(app * x) const {
        return m_imp->m_stack.is_eliminated(x);
    }
    
    void preprocessor::convert(model_ref & m) {
        return m_imp->m_stack.convert(m);
    }

    void preprocessor::display(std::ostream & out) const {
        m_imp->m_stack.display(out, "solver");
    }

    void preprocessor::set_cancel(bool f) {
        m_imp->set_cancel(f);
    }

};
