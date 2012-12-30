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
#include"lbool.h"

namespace mcsat {

    class bool_plugin : public plugin {
        symbol             m_name;
        ptr_vector<clause> m_watches;
        svector<lbool>     m_assignment;
        ptr_vector<trail>  m_justification; 
        svector<unsigned>  m_activity;
        unsigned           m_activity_inc;
        volatile bool      m_cancel;
    public:
        bool_plugin() {
            m_name         = "Boolean";
            m_activity_inc = 128;
            m_cancel       = false;
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
        }
       
        virtual plugin * clone() {
            return alloc(bool_plugin);
        }

        virtual bool internalize(node t, internalization_context & ctx) {
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
