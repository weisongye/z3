/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_trail.h

Abstract:

    Trail is the main component of the MCSat Kernel.
    It is also the communication bus for all MCSat components.
    
    For more details see the paper:
    "A model-constructing satisfiability calculus", VMCAI'13

Author:

    Leonardo de Moura (leonardo) 2012-12-14

Revision History:

*/
#ifndef _MCSAT_TRAIL_H_
#define _MCSAT_TRAIL_H_

#include"ast.h"
#include"mcsat_literal.h"
#include"mcsat_value.h"
#include"region.h"

namespace mcsat {
    class plugin;
    class expr_manager;

    typedef unsigned trail_kind;

    const trail_kind k_propagated_literal    = 0;
    const trail_kind k_propagated_eq         = 1;
    const trail_kind k_propagated_diseq      = 2;
    const trail_kind k_decided_literal       = 3;
    const trail_kind k_assumed_literal       = 4;
    const trail_kind k_model_assignment      = 5;
    const trail_kind k_assign_interp         = 6;
    const trail_kind k_assign_func_interp    = 7;
    const trail_kind k_first_extra           = 100;

    /**
       \brief Abstract class for "trail elements" as described in the paper:
       "A model-constructing satisfiability calculus", VMCAI'13

       Trail elements are decisions and propagations.

       Plugins may create new trail objects (e.g., propagated_bound).
       However, no trail object should require a destructor.
       
       Moreover, if a propagator needs more information/context for 
       explaining the propagation, it should store it inside the plugin.
    */
    class trail {
        friend class kernel;
        // The fields m_scope_lvl and m_mark are used by the kernel during 
        // conflict resolution.
        unsigned m_scope_lvl:31; 
        unsigned m_mark:1;
        unsigned scope_lvl() const { return m_scope_lvl; }
        bool is_marked() const { return m_mark != 0; }
        void mark(bool f) { m_mark = f; }
    public:
        trail():m_scope_lvl(0), m_mark(0) {}
        /**
           \brief Return true if the trail is a decision.
        */
        virtual bool is_decision() const;

        /**
           \brief Return true if the trail is an assumption.
           Assumptions are a special kind of decision used for tracking
           unsatisfiable cores.
        */
        virtual bool is_assumption() const;

        /**
           \brief Return the literal associated with this trail element.
           It returns null_literal if there is no literal associated with it.
           For example, model assignments do not have literals associated with them.
        */
        virtual literal lit() const;

        virtual trail_kind kind() const = 0;
    };

    typedef ptr_vector<trail> trail_vector;

    class model_decision;
    
    typedef ptr_vector<model_decision> model_decision_vector;

    // -----------------------------------
    //
    // Propagations
    //
    // -----------------------------------
    class propagation;

    /**
       \brief A propagation can be performed by any object that knows how to explain it.
    */
    class propagator {
    public:
        /**
           \brief Store into antecedents and new_antecedents an explanation for consequent.

           literal_antecedents AND trail_antecedents AND new_antecedents IMPLIES consequent 
           
           (modulo the assertions in the problem).

           If proof generation is enabled, then a proof should be stored in pr.
           
           If (literal_antecedents AND trail_antecedents AND new_antecedents IMPLIES consequent) is a valid formula,
           then the propagator may leave pr == 0. In this case, the propagator is assuming
           that it is trivial to check the valid formula.

           The new_antecedents must be false in the partial model induced by the current trail.
           For each new_antecedents[i] we have that decisions[i] is a trail that makes new_antecedents[i] false.
           That is, the trail stack is of the form
           
                   M decisions[i] ...
           
           new_antecedents[i] evaluates to false in 
           
                   M decisions[i]

           but is undefined in
           
                   M
        */
        virtual void explain(propagation & consequent, 
                             literal_vector & literal_antecedents, 
                             trail_vector & trail_antecedents, 
                             expr_ref_vector & new_antecedents, 
                             model_decision_vector & decisions,
                             proof_ref & pr) = 0;
        
        /**
           \brief This method in only invoked when:
               - Proof generation is enabled.
               - consequent.lit() == null_literal 
               - consequent is not propagated_eq nor propagated_diseq 

           Example: a module that perform bound propagation but does not want to create
           a literal for each propagated bound.
        */
        virtual expr * consequent_as_expr(propagation & consequent, expr_manager & m);
    };

    /**
       \brief Any fact propagated based on the set of clauses
       and facts already in the trail.
       
       The propagator must be capable of explaining this fact.
       In most cases the propagator is a plugin.
    */
    class propagation : public trail {
        propagator & m_propagator;
    public:
        propagation(propagator & p):m_propagator(p) {}
        propagator & get_propagator() const { return m_propagator; }
    };
    
    /**
       \brief A propagated literal.
    */
    class propagated_literal : public propagation {
        literal m_literal;
    public:
        propagated_literal(literal const & l, propagator & p):propagation(p), m_literal(l) {}

        virtual literal lit() const;

        virtual trail_kind kind() const;
    };

    /**
       \brief An equality propagated by a plugin.

       This kind of object is not really necessary.  It only exists to
       avoid the creation of an equality lhs = rhs and its associated
       node.
    */
    class propagated_eq : public propagation {
        node m_lhs;
        node m_rhs;
    public:
        propagated_eq(node lhs, node rhs, propagator & p):propagation(p), m_lhs(lhs), m_rhs(rhs) {}

        node lhs() const { return m_lhs; }
        node rhs() const { return m_rhs; }

        virtual trail_kind kind() const;
    }; 

    /**
       \brief A disequality propagated by a plugin.

       This kind of object is not really necessary.  It only exists to
       avoid the creation of an equality lhs = rhs and its associated
       node.
    */
    class propagated_diseq : public propagation {
        node m_lhs;
        node m_rhs;
    public:
        propagated_diseq(node lhs, node rhs, propagator & p):propagation(p), m_lhs(lhs), m_rhs(rhs) {}

        node lhs() const { return m_lhs; }
        node rhs() const { return m_rhs; }

        virtual trail_kind kind() const;
    }; 
    
    // -----------------------------------
    //
    // Decisions
    //
    // -----------------------------------

    /**
       \brief Decision (aka case-splits) is a super class
       for all forms of decision in the MCSat framework.
       Examples: decided literals and model assignments.
    */
    class decision : public trail {
    public:
        virtual bool is_decision() const;
    };

    /**
       \brief A Boolean decision.
    */
    class decided_literal : public decision {
        literal m_literal;
    public:
        decided_literal(literal l):m_literal(l) {}
        virtual literal lit() const;

        virtual trail_kind kind() const;
    };

    /**
       \brief Special kind of decision used to track unsat-cores.
    */
    class assumed_literal : public decided_literal {
    public:
        assumed_literal(literal l):decided_literal(l) {}
        virtual bool is_assumption() const;

        virtual trail_kind kind() const;
    };

    /**
       \brief A decision related to model construction.
    */
    class model_decision : public decision {
    public:
    };
    
    /**
       \brief A model assignment.
       
       In this implementation, a model assignment is slightly different from the one
       in the paper:

       "A model-constructing satisfiability calculus", VMCAI'13
       
       This decision assigns a node to an "abstract" value.
       The actual value is assigned using the assign_interpretation object.
       
       Motivations:

       1) Most theories are disjoint, so it only matters whether two different
       nodes are assigned to the same value or not. The actual representation
       is irrelevant for the combination problem. Thus, we can assign it later.
       
       2) It also enables scenarios where a plugin for the theory of arrays
       may assign two indices i and j two different values. These indices
       may be integers, and the theory of arrays don't know anything about
       integers, but it may say that in the model it is building i and j
       are assigned to two different values. The plugin for the theory of 
       arithmetic is the one responsible for creating the assign_interpretation
       object that will provide the actual interpretation.
       
       We also have func_assign_interpretation object for assigning
       interpretations to uninterpreted functions.
    */
    class model_assignment : public model_decision {
        node  m_node;
        value m_value;
    public:
        model_assignment(node n, value v):m_node(n), m_value(v) {}

        node  var() const { return m_node; }
        value val() const { return m_value; }

        virtual trail_kind kind() const;
    };
    
    class assign_interpretation : public model_decision {
        value  m_value;
        expr * m_interp;
    public:
        assign_interpretation(value v, expr * interp):m_value(v), m_interp(interp) {}

        value val() const { return m_value; }
        expr * interp() const { return m_interp; }

        virtual trail_kind kind() const;
    };

    class assign_func_interpretation : public model_decision {
        func_decl * m_f;
        expr *      m_interp;
    public:
        assign_func_interpretation(func_decl * f, expr * interp):m_f(f), m_interp(interp) {}

        func_decl * decl() const { return m_f; }
        expr * interp() const { return m_interp; }

        virtual trail_kind kind() const;
    };

    // -----------------------------------
    //
    // Manager
    //
    // -----------------------------------

    /**
       \brief Auxiliary class for creating trail objects.
    */
    class trail_manager {
        friend class kernel;
        region   m_region;
        unsigned m_next_kind;

        trail_manager();
        ~trail_manager();
        void push();
        void pop(unsigned num_scopes);
        /**
           \brief Create a new trail kind. This method is used by 
           plugin that need to create new kinds of propagation objects.
        */
        trail_kind mk_kind();
    public:
        template<typename T>
        T * mk(T const & t) {
            return new (m_region) T(t);
        }
    };

    class trail_stack {
        friend class kernel;
        ptr_vector<trail> m_stack;
        unsigned_vector   m_scopes;
        unsigned_vector   m_plugin_qhead;
        unsigned size() const { return m_stack.size(); }
        trail * operator[](unsigned i) const { return m_stack[i]; }
        // Return the end of the given level.
        unsigned end_lvl(unsigned lvl) const;
    public:
        trail_stack();
        ~trail_stack();
        void push();
        void pop(unsigned num_scopes);
        void push_back(trail * t);
        trail * next(unsigned pidx);
        bool fully_propagated() const;
    };
    
};    

#endif
