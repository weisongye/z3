/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_plugin.h

Abstract:

    An extension for the mcsat kernel.
    Plugins are used to add:
       - new theory solvers
       - propagators (for pruning the seach space)
       - and any other form of object that can interact with the trail.
Author:

    Leonardo de Moura (leonardo) 2012-12-16

Revision History:

*/
#ifndef _MCSAT_PLUGIN_H_
#define _MCSAT_PLUGIN_H_

#include"ast.h"
#include"params.h"
#include"ref.h"
#include"statistics.h"
#include"mcsat_trail.h"
#include"mcsat_node_attribute.h"

namespace mcsat {
    class expr_manager;
    class clause;

    /**
       \brief MCSat plugins do *not* have direct access to the MCSat kernel.
       They can access limited functionality using contexts provided to them.
       The initialization context provides the functionality available when
       a plugin is added into the kernel.
    */
    class initialization_context {
    public:
        virtual bool proofs_enabled() const = 0;
        virtual family_id get_family_id(char const * n) = 0;
        virtual node_uint_attribute & mk_uint_attribute() = 0;
        virtual node_double_attribute & mk_double_attribute() = 0;
        virtual trail_kind mk_trail_kind() = 0;
    };


    /**
       \brief MCSat plugins do *not* have direct access to the MCSat kernel.
       They can access limited functionality using contexts provided to them.
       The internalization context provide the functionality available when
       clauses are internalized in the kernel.
       
       This context is provided to the following method:

       bool plugin::internalize_clause(clause * c, clause_internalization_context & ctx);
    */
    class clause_internalization_context {
    public:
        /**
           Reference to the expr_manager that can be used to create new expressions.
        */
        virtual expr_manager & em() = 0;
        /**
           When a plugin is internalizing a clause c in
           
           bool plugin::internalize_clause(clause * c, clause_internalization_context & ctx);
           
           OR a node n in
           
           bool plugin::internalize(node n, internalization_context & ctx);
           
           it may need to propagate. This method returns a reference to 
           the trail object manager.
        */
        virtual trail_manager & tm() = 0;
        /**
           When a plugin is internalizing a node n in

           bool plugin::internalize(node n, internalization_context & ctx);
           
           it may need to propagate, this method adds a new propagation object
           to the trail.
        */
        virtual void add_propagation(propagation * p) = 0;
    };

    /**
       \brief MCSat plugins do *not* have direct access to the MCSat kernel.
       They can access limited functionality using contexts provided to them.
       The internalization context provide the functionality available when
       expressions are internalized in the kernel.
       
       This context is provided to the following method:

       bool plugin::internalize(node n, internalization_context & ctx);

       \remark This is an extension of the clause_internalization_context.
    */
    class internalization_context : public clause_internalization_context {
    public:
        /**
           \brief Return the expression associated with the given node.
        */
        virtual expr * to_expr(node n) = 0;
        /**
           \brief Return a node for the given expression. If a node did not exist
           for the given expression yet, then it is added to the internalization queue.
           This is the main API used during internalization.
        */
        virtual node mk_node(expr * n) = 0;
        /**
           When a plugin is internalizing a node n in

           bool plugin::internalize(node n, internalization_context & ctx);
           
           it may decide to include auxiliary axioms to MCSat state.
           The kernel assumes the axiom is relevant only when n is relevant.
           The proof pr is optional, and it is ignored when proof generation is disabled.
        */
        virtual void add_axiom(expr * ax, proof_ref & pr) = 0;
        /**
           Create a new auxiliary clause.
        */
        virtual clause * mk_clause(unsigned sz, literal const * lits, proof * pr) = 0;
    };

    /**
       \brief MCSat plugins do *not* have direct access to the MCSat kernel.
       They can access limited functionality using contexts provided to them.
       The propagation context provide the functionality available when
       a plugin is reading the "trail" and adding new propagations to it.

       This context is provided to the following method:

       void plugin::propagate(propagation_context & ctx);
    */
    class propagation_context { 
    public:
        /**
           \brief Return a reference to the trail object manager. A plugin
           needs this reference to be able to create new trail objects.
        */
        virtual trail_manager & tm() = 0;
        /**
           \brief Read the next trail object in the trail. The trail is the
           communication bus between plugins.
        */
        virtual trail * next() = 0;
        /**
           \brief Add a new propagation object to the trail.
        */
        virtual void add_propagation(propagation * p) = 0;
        /**
           \brief Add a new auxiliary axiom.

           \remark The new axiom \c ax will only be internalized after
           the method plugin::propagate returns.
           
           Application: quantifier instantiation.
        */
        virtual void add_axiom(expr * ax, proof_ref & pr) = 0;
    };

    /**
       \brief MCSat plugins do *not* have direct access to the MCSat kernel.
       They can access limited functionality using contexts provided to them.
       The propagation context provide the functionality available when a 
       plugin is performing a decision.

       This context is provided to the following method:

       decision * plugin::decide(decision_context & ctx);
    */
    class decision_context {
    public:
        /**
           Reference to the expr_manager that can be used to create new values.
        */
        virtual expr_manager & em() = 0;

        /**
           \brief Create new abstract value.
        */
        virtual value mk_value() = 0;
    };

    /**
       An extension for the mcsat kernel.
       Plugins are used to add:
       - new theory solvers
       - propagators (for pruning the seach space)
       - and any other form of object that can interact with the trail.
    */
    class plugin : public propagator {
        unsigned m_ref_count;
    public:
        virtual ~plugin();

        void inc_ref() { m_ref_count++; }
        void dec_ref() { SASSERT(m_ref_count > 0); m_ref_count--; if (m_ref_count == 0) dealloc(this); }

        // -----------------------------------
        //
        // Basic 
        //
        // -----------------------------------

        /**
           \brief Return the name of the plugin.
        */
        virtual symbol const & get_name() const = 0;

        /**
           \brief Update the set of parameters of this plugin.
        */
        virtual void updt_params(params_ref const & p);
        
        /**
           \brief Collect a description of the given parameters.
        */
        virtual void collect_param_descrs(param_descrs & r);
        
        /**
           \brief Collect performance statistics.
        */
        virtual void collect_statistics(statistics & st) const;

        /**
           \brief Interrupt plugin.
        */
        virtual void set_cancel(bool f);

        /**
           \brief Display the internal state of the plugin.
           It is only used for debugging purposes.
        */
        virtual void display(std::ostream & out) const;

        // -----------------------------------
        //
        // Backtracking 
        //
        // -----------------------------------

        /**
           \brief Mark a bracktracking point
           A backtracking point is created whenever a decision is performed.
        */
        virtual void push() = 0; 

        /**
           \brief Restore backtracking point.
        */
        virtual void pop(unsigned num_scopes) = 0;

        // -----------------------------------
        //
        // Initialization and cloning 
        //
        // -----------------------------------

        /**
           \brief Initialize the plugin in.
        */
        virtual void init(initialization_context & ctx) = 0;
       
        /**
           \brief Create a copy of the plugin.
        */
        virtual plugin * clone() = 0;

        // -----------------------------------
        //
        // Internalizing/compiling expressions.
        //
        // -----------------------------------
        
        /**
           \brief When assertions are added to the kernel, they are internalized
           into the plugins using this method.

           The protocol used is the following:

           1) For each plugin in the kernel, the method internalize is invoked until
              one plugin returns true. If none of them can handle the node n,
              then the kernel throws an exception to indicate the problem cannot
              be handled.
              When a plugin returns "true", it means it is responsible for building
              an interpretation for n.
              
              Note that the kernel invokes the plugin in the order they were registered
              in the kernel. A plugin wrapper/adapter can be used to enforce different
              internalization strategies.
              
           2) Plugins should use \c ctx.to_expr(n) to obtain the expression associated with \c n.
              The communication during the search is performed using nodes
              instead of expressions. 
              The context also provided the mehtod ctx.mk_node that allows the plugin to create
              nodes (if they do not already exist) for sub-expressions.
              Moreover, when a new node is created, it automatically 
              enters the todo queue of nodes to be internalized.

              Example: suppose we have a plugin P for propositional logic.
              and n is the node associated with the expression
                   (iff (> x 10) (not (> y 10)))
              P invokes ctx.mk_node to create nodes for
                   (> x 10) and (> y 10)
              Using these nodes, the plugin can create propagation rules to enforce
              that n is true iff ( (> x 10) is true IFF (not (> y 10)) is true ) 
              The nodes for (> x 10) and (> y 10) are added to the internalization
              queue if they were not associated to a a node before.
           
           3) During internalization some plugins may need to add new axioms.
              The functor \c ctx.add_axiom(n, pr) can be used to do that, where \c n is the expression
              to be asserted.
        */
        virtual bool internalize(node n, internalization_context & ctx) = 0;
        
        /**
           \brief When assertions are added to the kernel or conflicts are resolved, the kernel may create clauses.
           One of the plugins must be responsible for making sure the clause is satisfied.
           
           When a plugin returns "true", it means it is responsible for making sure the clause is satisfied.
        */
        virtual bool internalize(clause * c, clause_internalization_context & ctx);

        // -----------------------------------
        //
        // Propagation
        //
        // -----------------------------------

        /**
           \brief New facts added to the trail can be read using the method ctx.next().
           ctx.next() method returns 0 if there are no more new facts in the trail.
           A new propagation can be added to the trail using ctx.add_propagation. 
           A conflict is set by propagating false.
        */
        virtual void propagate(propagation_context & ctx) = 0;
        
        /**
           \brief Similar to \c propagate, but is only invoked by the kernel when the propagate of every plugin
           does not modify the trail, and none of the plugins need to perform a decision (aka case-split).

           This method is usually used to implement "expensive" propagation steps.

           \remark Plugin wrappers may change the default behavior described above.
        */
        virtual void full_propagate(propagation_context & ctx);

        // -----------------------------------
        //
        // Decision
        //
        // -----------------------------------

        /**
           \brief By default, the kernel uses the following protocol to select which plugin
           will perform a decision. 

           1) Invokes the priority() method of each plugin. The plugin P that returns the highest 
           value is selected to perform the decision (aka case-split). Ties are broken
           based on the order the plugins were added to the kernel.
           If priority returns 0, then the kernel assumes this plugin does not need to perform a decision.

           2) The method plugin::prepare_decision of P is invoked. This method allows the plugin
           to internalize new expressions. This is needed when a plugin wants to perform a decision
           on an expression n that is part of the finite basis but was not internalized yet.
           Remark: the kerne will perform propagation before it continues the following steps.
           Moreover, the process is interrupted if a conflict is detected.

           3) The method plugin::push of every plugin is invoked.

           4) The method plugin::decide of P is invoked.
        */
        virtual unsigned priority() const;
        
        /**
           \sa priority
        */
        virtual void prepare_decision(internalization_context & ctx);
        
        /**
           \brief Final step in the decision protocol described above.
           If the plugin returns 0, the kernel ignores the result and
           restarts the decision making process (step 1 above).

           \sa priority
        */
        virtual decision * decide(decision_context & ctx) = 0;
    };

    typedef ref<plugin>         plugin_ref;
    typedef sref_vector<plugin> plugin_ref_vector;
};

#endif
