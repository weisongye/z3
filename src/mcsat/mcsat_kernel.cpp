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
#include"mcsat_exception.h"
#include"mcsat_plugin.h"

namespace mcsat {

    struct kernel::imp {
        typedef std::pair<expr *, proof *> expr_proof_pair;
        typedef svector<expr_proof_pair>   expr_proof_pair_vector;
        typedef svector<node>              node_queue;

        bool                      m_fresh;
        bool                      m_proofs_enabled;
        expr_manager              m_expr_manager;
        node_manager              m_node_manager;
        node_attribute_manager    m_attribute_manager;
        value_manager             m_value_manager;
        trail_manager             m_trail_manager;
        clause_manager            m_clause_manager;
        plugin_ref_vector         m_plugins;
        trail_stack               m_trail_stack;
        node_queue                m_to_internalize; // internalization todo queue.
        expr_proof_pair_vector    m_new_axioms;     // auxiliary axioms created by plugins.
        basic_recognizers         m_butil;

        volatile bool             m_cancel;
        
        class init_ctx : public initialization_context {
            imp & m;
        public:
            init_ctx(imp & _m):m(_m) {}
            virtual bool proofs_enabled() const { return m.m_proofs_enabled; }
            virtual family_id get_family_id(char const * n) { return m.m_expr_manager.get_family_id(n); }
            virtual node_uint_attribute &   mk_uint_attribute() { return m.m_attribute_manager.mk_uint_attribute(); }
            virtual node_double_attribute & mk_double_attribute() { return m.m_attribute_manager.mk_double_attribute(); }
            virtual trail_kind mk_trail_kind() { return m.m_trail_manager.mk_kind(); }
        };

        class internalization_ctx : public internalization_context {
            imp &                    m;
        public:
            internalization_ctx(imp & _m):m(_m) {}
            
            virtual expr_manager & em() { 
                return m.m_expr_manager;
            }

            virtual expr * to_expr(node n) { 
                return m.m_node_manager.to_expr(n);
            }

            virtual node mk_node(expr * n) { 
                if (m.m_node_manager.contains(n)) {
                    return m.m_node_manager.mk_node(n);
                }
                else {
                    node r = m.m_node_manager.mk_node(n);
                    m.m_to_internalize.push_back(r);
                    return r;
                }
            }
            
            virtual void add_axiom(expr * ax, proof_ref & pr) {
                m.m_new_axioms.push_back(expr_proof_pair(ax, pr));
            }

            virtual trail_manager & tm() {
                return m.m_trail_manager;
            }

            virtual void add_propagation(propagation * p) {
                m.m_trail_stack.push_back(p);
            }

            virtual clause * mk_clause(unsigned sz, literal const * lits, proof * pr) {
                return m.m_clause_manager.mk_aux(sz, lits, pr);
            }
        };

        class propagation_ctx : public propagation_context {
            imp &    m;
            unsigned m_pidx;
        public:
            propagation_ctx(imp & _m, unsigned pidx):m(_m), m_pidx(pidx) {}

            virtual trail_manager & tm() {
                return m.m_trail_manager;
            }

            virtual trail * next() {
                return m.m_trail_stack.next(m_pidx);
            }

            virtual void add_propagation(propagation * p) {
                m.m_trail_stack.push_back(p);
            }

            virtual void add_axiom(expr * ax, proof_ref & pr) {
                m.m_new_axioms.push_back(expr_proof_pair(ax, pr));
            }
        };

        imp(ast_manager & m, bool proofs_enabled):
            m_expr_manager(m),
            m_attribute_manager(m_node_manager),
            m_butil(m.get_basic_family_id()) {
            m_proofs_enabled = proofs_enabled;
            m_fresh  = true;
            m_cancel = false;
        }

        // Return true if the kernel is "fresh" and assertions were not added yet.
        bool is_fresh() const {
            return m_fresh;
        }

        void add_plugin(plugin * p) {
            init_ctx ctx(*this);
            SASSERT(is_fresh());
            p = p->clone();
            m_plugins.push_back(p);
            p->init(ctx);
        }

        unsigned num_plugins() const {
            return m_plugins.size();
        }

        plugin & p(unsigned i) const {
            return *(m_plugins.get(i));
        }

        // -----------------------------------
        //
        // Internalization
        //
        // -----------------------------------

        void internalize_core(node n) {
            internalization_ctx ctx(*this);
            for (unsigned i = 0; i < num_plugins(); i++) {
                if (p(i).internalize(n, ctx))
                    return;
            }
            throw exception("MCSat could not handle the problem: none of existing plugins could process one of the expressions");
        }

        node internalize(expr * n) {
            SASSERT(m_to_internalize.empty());
            node r = m_node_manager.mk_node(n);
            internalize_core(r);
            while (!m_to_internalize.empty()) {
                node n = m_to_internalize.back();
                m_to_internalize.pop_back();
                internalize_core(n);
            }
            return r;
        }

        literal internalize_literal(expr * n) {
            expr * atom;
            if (m_butil.is_not(n, atom))
                return literal(internalize(atom), true);
            else
                return literal(internalize(n), false);
        }

        void assert_expr_core(expr * f, proof * pr, bool main) {
            internalization_ctx ctx(*this);
            unsigned num_lits;
            expr * const * lits;
            if (m_butil.is_or(f)) {
                lits     = to_app(f)->get_args();
                num_lits = to_app(f)->get_num_args();
            }
            else {
                lits     = &f;
                num_lits = 1;
            }
            literal_vector new_lits;
            for (unsigned i = 0; i < num_lits; i++) {
                literal l = internalize_literal(lits[i]);
                new_lits.push_back(l);
            }
            clause * c;
            if (main)
                c = m_clause_manager.mk(new_lits.size(), new_lits.c_ptr(), pr);
            else
                c = m_clause_manager.mk_aux(new_lits.size(), new_lits.c_ptr(), pr);
            for (unsigned i = 0; i < num_plugins(); i++) {
                if (p(i).internalize(c, ctx))
                    return; // found plugin to process the clause
            }
            throw exception("MCSat could not handle the problem: none of existing plugins could process one of the input clauses");
        }
        
        void assert_expr(expr * f, proof * pr) {
            m_fresh = false;
            SASSERT(m_to_internalize.empty());
            assert_expr_core(f, pr, true);
            while (!m_new_axioms.empty()) {
                expr_proof_pair p = m_new_axioms.back();
                m_new_axioms.pop_back();
                assert_expr_core(p.first, p.second, false);
            }
        }
        
        // -----------------------------------
        //
        // Backtracking & conflict resolution
        //
        // -----------------------------------

        void push(bool user) {
            SASSERT(m_new_axioms.empty());
            SASSERT(m_to_internalize.empty());
            m_expr_manager.push();
            m_node_manager.push();
            m_value_manager.push();
            m_trail_manager.push();
            m_clause_manager.push(user);
            m_trail_stack.push();
            unsigned sz = m_plugins.size();
            for (unsigned i = 0; i < sz; i++) {
                m_plugins.get(i)->push();
            }
        }

        void pop(unsigned num_scopes, bool user) {
            unsigned sz = m_plugins.size();
            for (unsigned i = 0; i < sz; i++) {
                m_plugins.get(i)->pop(num_scopes);
            }
            m_trail_stack.pop(num_scopes);
            m_clause_manager.pop(num_scopes, user);
            m_trail_manager.pop(num_scopes);
            m_value_manager.pop(num_scopes);
            m_node_manager.pop(num_scopes);
            m_expr_manager.pop(num_scopes);
        }

        // -----------------------------------
        //
        // Propagation
        //
        // -----------------------------------
        
        void propagate() {
            
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
            for (unsigned i = 0; i < num_plugins(); i++) {
                p(i).set_cancel(f);
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
        m_imp->push(true);
    }
     
    void kernel::pop(unsigned num_scopes) {
        m_imp->pop(true, num_scopes);
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
