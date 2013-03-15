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
#include"mcsat_trail.h"
#include"tptr.h"
#include"lbool.h"

namespace mcsat {

    /**
       \brief Marks a conflicting trail that contains l and (not l).
    */
    class l_not_l_conflict : public conflict {
        class prop : public propagator {
            propagated_literal * m_l; // l occurs after (not l), thus it can't be a decision.
            trail *              m_not_l;
        public:
            prop(propagated_literal * l, trail * not_l):m_l(l), m_not_l(not_l) {}
            virtual void explain(propagation & consequent, trail_vector & antecedents, expr_ref_vector & new_antecedents, proof_ref & pr) { UNREACHABLE(); }
            virtual void explain_conflict(trail_vector & antecedents, expr_ref_vector & new_antecedents, proof_ref & pr) {
                antecedents.push_back(m_l);
                antecedents.push_back(m_not_l);
            }
        };
        prop m_prop;
    public:
        l_not_l_conflict(propagated_literal * l, trail * not_l):conflict(m_prop), m_prop(l, not_l) {}
    };

    class propagated_clause_literal : public propagated_literal {
        clause * m_clause;
    public:
        propagated_clause_literal(literal const & l, clause * c, propagator & p):
            propagated_literal(l, p),
            m_clause(c) {
            // m_clause may be 0 (NULL)
            // the bool_plugin also uses propagated_clause_literal to justify the literal true.
        }
        propagated_clause_literal(literal const & l, propagator & p):
            propagated_literal(l, p),
            m_clause(0) {
        }
        clause * get_clause() const { return m_clause; }
    };

    class bool_plugin : public plugin {
        symbol                 m_name;
        basic_recognizers      m_util;
        bool                   m_proofs_enabled;
        vector<clause_vector>  m_watches;
        svector<lbool>         m_assignment;
        ptr_vector<trail>      m_justification;
        node_uint_attribute *  m_activity;
        unsigned               m_activity_inc;
        literal_vector         m_local_trail;
        // When a conflict is detected, m_conflict_l contains a literal l such that (not l) is also in the trail.
        literal                m_conflict_l; 
        // Justification for m_conflict_l. 
        // Note that, m_justification[m_conflict_l.var().index()] contains the justification for (not l).
        trail *                m_conflict_justification; 
        struct scope {
            unsigned           m_local_trail_lim;
        };
        svector<scope>         m_scopes;
        volatile bool          m_cancel;

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
            SASSERT(m_conflict_l == null_literal);
            m_scopes.push_back(scope());
            scope & s = m_scopes.back();
            s.m_local_trail_lim = m_local_trail.size();
        }

        void unassign_literals(unsigned old_sz) {
            unsigned i = m_local_trail.size();
            while (i > old_sz) {
                --i;
                literal l = m_local_trail[i];
                m_assignment[l.index()]          = l_undef;
                m_assignment[(~l).index()]       = l_undef;
                m_justification[l.var().index()] = 0;
            }
            m_local_trail.shrink(old_sz);
        }

        virtual void pop(unsigned num_scopes) {
            unsigned new_lvl = m_scopes.size() - num_scopes;
            scope & s           = m_scopes[new_lvl];
            unassign_literals(s.m_local_trail_lim);
            m_scopes.shrink(new_lvl);
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
                m_justification.resize(new_sz);
            }
            SASSERT(idx < m_justification.size());
            literal l(n, false);
            unsigned l_idx          = l.index();
            unsigned not_l_idx      = (~l).index();
            m_assignment[l_idx]     = l_undef;
            m_assignment[not_l_idx] = l_undef;
            m_watches[l_idx]        .reset();
            m_watches[not_l_idx]    .reset();
            m_justification[idx]    = 0;
            m_activity              ->set(n, 0);
        }

        lbool get_value(literal l) {
            return m_assignment[l.index()];
        }

        void assign_value(literal l, trail * t) {
            SASSERT(get_value(l) == l_undef);
            m_local_trail.push_back(l);
            m_assignment[l.index()]          = l_true;
            m_assignment[~l.index()]         = l_false;
            m_justification[l.var().index()] = t;
        }

        void propagate_literal(literal l, clause * c, internalization_context & ctx) {
            if (m_conflict_l == null_literal)
                return;
            if (get_value(l) == l_true) {
                // nothing to be done
                return; 
            }
            else {
                propagated_literal * p = ctx.tm().mk(propagated_clause_literal(l, c, *this));
                if (get_value(l) == l_false) {
                    // conflict
                    SASSERT(m_conflict_l == null_literal);
                    m_conflict_l             = l;
                    m_conflict_justification = p;
                    ctx.add_propagation(p);
                    ctx.add_propagation(ctx.tm().mk(l_not_l_conflict(p, m_justification[l.var().index()])));
                }
                else {
                    assign_value(l, p);
                    ctx.add_propagation(p);
                }
            }
        }

        void internalize_true(node n, internalization_context & ctx) {
            init_bvar(n);
            literal l(n, false);
            propagation * p = ctx.tm().mk(propagated_clause_literal(l, *this));
            assign_value(l, p);
            ctx.add_propagation(p);
        }

        void internalize_false(node n, internalization_context & ctx) {
            init_bvar(n);
            literal l(n, true);
            propagation * p = ctx.tm().mk(propagated_clause_literal(~l, *this));
            assign_value(~l, p);
            ctx.add_propagation(p);
        }

        virtual bool internalize(node n, internalization_context & ctx) {
            expr * t = ctx.to_expr(n);
            if (is_app(t) && m_util.is_bool(get_sort(t))) {
                if (to_app(t)->get_family_id() == m_util.get_family_id()) {
                    switch (to_app(t)->get_decl_kind()) {
                    case OP_TRUE:
                        internalize_true(n, ctx);
                        return true;
                    case OP_FALSE:
                        internalize_false(n, ctx);
                        return true;
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
            // TODO
            return false;
        }

        virtual void dettach_clause(clause * c) {
            // TODO
        }

        virtual void propagate(propagation_context & ctx) {
            // TODO
        }
        
        virtual void full_propagate(propagation_context & ctx) {
        }

        void inc_activity(node n) {
            // TODO
        }

        virtual void explain(propagation & consequent, trail_vector & antecedents, expr_ref_vector & new_antecedents, proof_ref & pr) {
            SASSERT(consequent.kind() == k_propagated_literal);
            literal l = consequent.lit();
            SASSERT(l != null_literal);
            node p = l.var();
            inc_activity(p);
            propagated_clause_literal * t;
            if (l == m_conflict_l) 
                t = static_cast<propagated_clause_literal*>(m_conflict_justification);
            else
                t = static_cast<propagated_clause_literal*>(m_justification[p.index()]);
            if (t->get_clause()) {
                clause const & c = *(t->get_clause());
                SASSERT(c[0] == l);
                unsigned sz = c.size();
                for (unsigned i = 1; i < sz; i++) {
                    literal const & l_prime = c[i];
                    antecedents.push_back(m_justification[l_prime.var().index()]);
                }
            }
        }

        virtual void explain_conflict(trail_vector & antecedents, expr_ref_vector & new_antecedents, proof_ref & pr) {
            UNREACHABLE();
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
