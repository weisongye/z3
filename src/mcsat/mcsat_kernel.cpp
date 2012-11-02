/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_kernel.cpp

Abstract:

    MCSAT kernel

Author:

    Leonardo de Moura (leonardo) 2012-11-01.

Revision History:

--*/
#include"mcsat_kernel.h"
#include"statistics.h"

namespace mcsat {

    struct kernel::imp {
        ast_manager & m_manager;
        
        imp(ast_manager & m, bool proofs_enabled, bool models_enabled, bool core_enabled):
            m_manager(m) {
        }
        
        ast_manager & m() const { return m_manager; }

        void assert_expr(expr * f, proof * pr, expr_dependency * d) {
        }
        
        void push() {
        }

        void pop(unsigned num_scopes) {
        }

        lbool check_sat(unsigned num_assumptions, expr * const * assumptions) {
            return l_undef;
        }

        void collect_statistics(statistics & st) const {
        }

        void get_unsat_core(ptr_vector<expr> & r) {
        }

        void get_model(model_ref & m) {
        }

        proof * get_proof() {
            return 0;
        }

        std::string reason_unknown() const {
            return "unknown";
        }

        void set_cancel(bool f) {
        }

        void display(std::ostream & out) const {
        }
    };
    
    kernel::kernel(ast_manager & m, bool proofs_enabled, bool models_enabled, bool core_enabled) {
    }

    kernel::~kernel() {
    }
   
    ast_manager & kernel::m() const {
        return m_imp->m();
    }
        
    void kernel::assert_expr(expr * f, proof * pr, expr_dependency * d) {
        m_imp->assert_expr(f, pr, d);
    }
        
    void kernel::push() {
        m_imp->push();
    }
     
    void kernel::pop(unsigned num_scopes) {
        m_imp->pop(num_scopes);
    }

    lbool kernel::check_sat(unsigned num_assumptions, expr * const * assumptions) {
        return m_imp->check_sat(num_assumptions, assumptions);
    }
    
    void kernel::collect_statistics(statistics & st) const {
        m_imp->collect_statistics(st);
    }
    
    void kernel::get_unsat_core(ptr_vector<expr> & r) {
        m_imp->get_unsat_core(r);
    }

    void kernel::get_model(model_ref & m) {
        m_imp->get_model(m);
    }
    
    proof * kernel::get_proof() {
        return m_imp->get_proof();
    }
    
    std::string kernel::reason_unknown() const {
        return m_imp->reason_unknown();
    }

    void kernel::set_cancel(bool f) {
        m_imp->set_cancel(f);
    }
    
    void kernel::display(std::ostream & out) const {
        m_imp->display(out);
    }

};
