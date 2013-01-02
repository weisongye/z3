/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_bool_plugin.cpp

Abstract:

    Standard plugin for propositional logic.
    
Author:

    Leonardo de Moura (leonardo) 2012-12-22

Revision History:

*/
#include"mcsat_plugin.h"
#include"mcsat_expr_manager.h"
#include"mcsat_clause.h"
#include"lbool.h"

namespace mcsat {

    class bool_plugin : public plugin {
        symbol                m_name;
        basic_recognizers     m_util;
        bool                  m_proofs_enabled;
        vector<clause_vector> m_watches;
        svector<lbool>        m_assignment;
        ptr_vector<clause>    m_justification;
        ptr_vector<trail>     m_ext_justification; 
        node_uint_attribute * m_activity;
        unsigned              m_activity_inc;
        volatile bool         m_cancel;

        node_uint_attribute & activity() { SASSERT(m_activity); return *m_activity; }

    public:
        bool_plugin() {
            m_name           = "Boolean";
            m_activity_inc   = 128;
            m_cancel         = false;
            m_activity       = 0;
            m_proofs_enabled = false;
        }

        virtual ~bool_plugin() {
        }

        virtual symbol const & get_name() const { 
            return m_name;
        }

        virtual void updt_params(params_ref const & p) {
        }
        
        virtual void collect_param_descrs(param_descrs & r) {
        }

        virtual void collect_statistics(statistics & st) const {
        }

        virtual void set_cancel(bool f) {
            m_cancel = f;
        }

        virtual void display(std::ostream & out) const {
        }

        virtual void push() {
        }

        virtual void pop(unsigned num_scopes) {
        }

        virtual void init(initialization_context & ctx) {
            m_util.set_family_id(ctx.get_family_id("basic"));
            m_activity       = &ctx.mk_uint_attribute();
            m_proofs_enabled = ctx.proofs_enabled();
        }
       
        virtual plugin * clone() {
            return alloc(bool_plugin);
        }

        void init_bvar(node n) {
            unsigned idx = n.index();
            if (idx >= m_justification.size()) {
                unsigned new_sz = idx + 1;
                m_assignment.resize(new_sz*2, l_undef);
                m_watches.resize(new_sz*2);
                m_justification.resize(new_sz, 0);
                m_ext_justification.resize(new_sz, 0);
            }
        }

        lbool get_value(literal l) {
            return m_assignment[l.index()];
        }

        void propagate_literal(literal l, clause * c, internalization_context & ctx) {
            if (get_value(l) == l_true) {
                // nothing to be done
                return; 
            }
            else if (get_value(l) == l_false) {
                // conflict
                
            }
            else {
                m_assignment[l.index()]  = l_true;
                m_assignment[~l.index()] = l_false;
                m_justification[l.var().index()] = c;
                ctx.add_propagation(ctx.tm().mk(propagated_literal(l, *this)));
            }
        }

        void internalize_true(node n, expr * t, internalization_context & ctx) {
            init_bvar(n);
            ctx.add_propagation(ctx.tm().mk(propagated_literal(literal(n, false), *this)));

        }

        virtual bool internalize(node n, internalization_context & ctx) {
            expr * t = ctx.to_expr(n);
            if (is_app(t) && m_util.is_bool(get_sort(t))) {
                if (to_app(t)->get_family_id() == m_util.get_family_id()) {
                    switch (to_app(t)->get_decl_kind()) {
                    case OP_TRUE:
                        init_bvar(n);
                        
                    case OP_FALSE:
                        init_bvar(n);
                    case OP_ITE:
                    case OP_AND:
                    case OP_OR:
                    case OP_EQ: 
                    case OP_IFF:
                    case OP_XOR:
                    case OP_NOT:
                    case OP_IMPLIES:
                    default:
                        return false;
                    }
                }
                else if (is_uninterp_const(t)) {
                    init_bvar(n);
                    return true;
                }
            }
            return false;
        }

        virtual bool internalize(clause * c, clause_internalization_context & ctx) {
            return false;
        }

        virtual void propagate(propagation_context & ctx) {
        }
        
        virtual void full_propagate(propagation_context & ctx) {
        }

        virtual void explain(propagation & consequent, trail_vector & antecedents, expr_ref_vector & new_antecedents, proof_ref & pr) {
        }

        virtual unsigned priority() const {
            return UINT_MAX;
        }
        
        virtual void prepare_decision(internalization_context & ctx) {
        }

        virtual decision * decide(decision_context & ctx) {
            return 0;
        }
    };

    plugin * mk_bool_plugin() {
        return alloc(bool_plugin);
    }

};
