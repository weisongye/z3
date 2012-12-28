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
#include"mcsat_expr_manager.h"
#include"mcsat_node_manager.h"
#include"mcsat_value_manager.h"
#include"mcsat_node_attribute.h"
#include"mcsat_clause_manager.h"
#include"mcsat_plugin.h"

namespace mcsat {

    struct kernel::imp {
        
        class _initialization_context : public initialization_context {
            node_attribute_manager & m_attr_manager;
        public:
            _initialization_context(node_attribute_manager & m):m_attr_manager(m) {}
            virtual node_uint_attribute &   mk_uint_attribute() { return m_attr_manager.mk_uint_attribute(); }
            virtual node_double_attribute & mk_double_attribute() { return m_attr_manager.mk_double_attribute(); }
        };

        bool                      m_fresh;
        bool                      m_proofs_enabled;
        expr_manager              m_expr_manager;
        node_manager              m_node_manager;
        node_attribute_manager    m_attribute_manager;
        value_manager             m_value_manager;
        clause_manager            m_clause_manager;
        plugin_ref_vector         m_plugins;
        ptr_vector<trail>         m_trail_stack;
        unsigned_vector           m_plugin_qhead;
        _initialization_context   m_init_ctx;

        volatile bool             m_cancel;

        imp(ast_manager & m, bool proofs_enabled):
            m_expr_manager(m),
            m_attribute_manager(m_node_manager),
            m_init_ctx(m_attribute_manager) {
            m_proofs_enabled = proofs_enabled;
            m_fresh  = true;
            m_cancel = false;
        }

        // Return true if the kernel is "fresh" and assertions were not added yet.
        bool is_fresh() const {
            return m_fresh;
        }

        void add_plugin(plugin * p) {
            SASSERT(is_fresh());
            p = p->clone();
            m_plugins.push_back(p);
            p->init(m_init_ctx);
        }

        // -----------------------------------
        //
        // Internalization
        //
        // -----------------------------------

        void assert_expr(expr * f, proof * pr) {
            m_fresh = false;
        }
        
        // -----------------------------------
        //
        // Backtracking & conflict resolution
        //
        // -----------------------------------

        void push() {
        }

        void pop(unsigned num_scopes) {
        }

        // -----------------------------------
        //
        // Search
        //
        // -----------------------------------

        lbool check_sat(unsigned num_assumptions, expr * const * assumptions) {
            if (is_fresh()) 
                return l_true;
            // TODO
            return l_undef;
        }

        void collect_statistics(statistics & st) const {
            // TODO
        }

        void get_unsat_core(ptr_vector<expr> & r) {
            // TODO
        }

        struct mk_model : public expr_manager::functor {
            model_ref & m_model;
            mk_model(model_ref & m):m_model(m) {}
            virtual void operator()(ast_manager & m, expr_manager::store_expr_functor & to_save) {
                m_model = alloc(model, m);
            }
        };

        void get_model(model_ref & md) {
            // TODO
            mk_model mk(md);
            m_expr_manager.apply(mk);
        }

        proof * get_proof() {
            return 0;
        }

        std::string reason_unknown() const {
            return "unknown";
        }

        void set_cancel(bool f) {
            m_cancel = f;
            for (unsigned i = 0; i < m_plugins.size(); i++) {
                m_plugins.get(i)->set_cancel(f);
            }
        }

        void display(std::ostream & out) const {
        }
    };
    
    kernel::kernel(ast_manager & m, bool proofs_enabled) {
        m_imp = alloc(imp, m, proofs_enabled);
    }

    kernel::~kernel() {
    }

    void kernel::add_plugin(plugin * p) {
        m_imp->add_plugin(p);
    }
   
    void kernel::assert_expr(expr * f, proof * pr) {
        m_imp->assert_expr(f, pr);
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
