/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_context.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-18.

Revision History:

--*/
#ifndef _DL_CONTEXT_H_
#define _DL_CONTEXT_H_

#ifdef _CYGWIN
#undef min
#undef max
#endif
#include"arith_decl_plugin.h"
#include"map.h"
#include"th_rewriter.h"
#include"str_hashtable.h"
#include"var_subst.h"
#include"dl_base.h"
#include"dl_costs.h"
#include"dl_decl_plugin.h"
#include"dl_relation_manager.h"
#include"dl_rule_set.h"
#include"pdr_dl_interface.h"
#include"dl_bmc_engine.h"
#include"tab_context.h"
#include"rel_context.h"
#include"lbool.h"
#include"statistics.h"
#include"params.h"
#include"trail.h"
#include"model_converter.h"
#include"model2expr.h"
#include"smt_params.h"
#include"dl_rule_transformer.h"
#include"expr_abstract.h"
#include"expr_functors.h"
#include"clp_context.h"

namespace datalog {

    enum execution_result {
        OK,
        TIMEOUT,
        MEMOUT,
        INPUT_ERROR,
        APPROX,
        CANCELED
    };

    class context {
    public:
        typedef unsigned finite_element;
        enum sort_kind {
            SK_UINT64,
            SK_SYMBOL
        };

    private:
        class sort_domain;
        class symbol_sort_domain;
        class uint64_sort_domain;
        class restore_rules;
        class contains_pred;

        typedef hashtable<symbol, symbol_hash_proc, symbol_eq_proc> symbol_set;
        typedef map<symbol, func_decl*, symbol_hash_proc, symbol_eq_proc> sym2decl;
        typedef obj_map<const func_decl, svector<symbol> > pred2syms;
        typedef obj_map<const sort, sort_domain*> sort_domain_map;

        class contains_pred : public i_expr_pred {
            context const& ctx;
        public:
            contains_pred(context& ctx): ctx(ctx) {}
            virtual ~contains_pred() {}
            
            virtual bool operator()(expr* e) {
                return ctx.is_predicate(e);
            }
        };


        ast_manager &      m;
        smt_params &       m_fparams;
        params_ref         m_params_ref;
        fixedpoint_params  m_params;
        dl_decl_util       m_decl_util;
        th_rewriter        m_rewriter;
        var_subst          m_var_subst;
        rule_manager       m_rule_manager;
        unused_vars_eliminator m_elim_unused_vars;
        expr_abstractor        m_abstractor;
        contains_pred      m_contains_p;
        check_pred         m_check_pred;
        rule_transformer   m_transf;
        trail_stack<context> m_trail;
        ast_ref_vector     m_pinned;
        app_ref_vector     m_vars;
        svector<symbol>    m_names;
        sort_domain_map    m_sorts;
        func_decl_set      m_preds;
        sym2decl           m_preds_by_name;
        pred2syms          m_argument_var_names;
        rule_set           m_rule_set;
        rule_set           m_transformed_rule_set;
        unsigned           m_rule_fmls_head;
        expr_ref_vector    m_rule_fmls;
        svector<symbol>    m_rule_names;
        expr_ref_vector    m_background;
        model_converter_ref m_mc;
        proof_converter_ref m_pc;

        rel_context*                    m_rel;
        scoped_ptr<engine_base>         m_engine;

        bool               m_closed;
        bool               m_saturation_was_run;
        execution_result   m_last_status;
        expr_ref           m_last_answer;
        DL_ENGINE          m_engine_type;
        volatile bool      m_cancel;



        bool is_fact(app * head) const;
        bool has_sort_domain(relation_sort s) const;
        sort_domain & get_sort_domain(relation_sort s);
        const sort_domain & get_sort_domain(relation_sort s) const;

        class engine_type_proc;


    public:
        context(ast_manager & m, smt_params& fp, params_ref const& p = params_ref());
        ~context();
        void reset();

        void push();
        void pop();
        
        bool saturation_was_run() const { return m_saturation_was_run; }
        void notify_saturation_was_run() { m_saturation_was_run = true; }

        void configure_engine();

        ast_manager & get_manager() const { return m; }
        rule_manager & get_rule_manager() { return m_rule_manager; }
        smt_params & get_fparams() const { return m_fparams; }
        fixedpoint_params const&  get_params() const { return m_params; }
        DL_ENGINE get_engine() { configure_engine(); return m_engine_type; }
        th_rewriter& get_rewriter() { return m_rewriter; }
        var_subst & get_var_subst() { return m_var_subst; }
        dl_decl_util & get_decl_util()  { return m_decl_util; }

        bool generate_proof_trace() const { return m_params.generate_proof_trace(); }
        bool output_profile() const { return m_params.output_profile(); }
        bool fix_unbound_vars() const { return m_params.fix_unbound_vars(); }
        symbol default_table() const { return m_params.default_table(); }
        symbol default_relation() const { return m_params.default_relation(); } // external_relation_plugin::get_name()); 
        symbol default_table_checker() const { return m_params.default_table_checker(); }
        bool default_table_checked() const { return m_params.default_table_checked(); }
        bool dbg_fpr_nonempty_relation_signature() const { return m_params.dbg_fpr_nonempty_relation_signature(); }
        unsigned dl_profile_milliseconds_threshold() const { return m_params.profile_timeout_milliseconds(); }
        bool all_or_nothing_deltas() const { return m_params.all_or_nothing_deltas(); }
        bool compile_with_widening() const { return m_params.compile_with_widening(); }
        bool unbound_compressor() const { return m_params.unbound_compressor(); }
        bool similarity_compressor() const { return m_params.similarity_compressor(); }
        unsigned similarity_compressor_threshold() const { return m_params.similarity_compressor_threshold(); }
        unsigned soft_timeout() const { return m_fparams.m_soft_timeout; }
        unsigned initial_restart_timeout() const { return m_params.initial_restart_timeout(); } 
        bool generate_explanations() const { return m_params.generate_explanations(); }
        bool explanations_on_relation_level() const { return m_params.explanations_on_relation_level(); }
        bool magic_sets_for_queries() const { return m_params.magic_sets_for_queries();  }
        bool eager_emptiness_checking() const { return m_params.eager_emptiness_checking(); }

        void register_finite_sort(sort * s, sort_kind k);

        /**
           Register uninterpreted constant to be used as an implicitly quantified variable.
           The variable gets quantified in the formula passed to rule::mk_rule_from_horn.
        */

        void register_variable(func_decl* var);

        expr_ref bind_variables(expr* fml, bool is_forall);

        /**
           Register datalog relation.

           If names is true, we associate the predicate with its name, so that it can be 
           retrieved by the try_get_predicate_decl() function. Auxiliary predicates introduced
           e.g. by rule transformations do not need to be named.
         */
        void register_predicate(func_decl * pred, bool named);

        /**
           Restrict reltaions to set of predicates.
         */
        void restrict_predicates(func_decl_set const& preds);

        /**
           \brief Retrieve predicates
        */
        func_decl_set const& get_predicates() const { return m_preds; }
        bool is_predicate(func_decl* pred) const { return m_preds.contains(pred); }
        bool is_predicate(expr * e) const { return is_app(e) && is_predicate(to_app(e)->get_decl()); }

        /**
           \brief If a predicate name has a \c func_decl object assigned, return pointer to it;
           otherwise return 0.
           
           Not all \c func_decl object used as relation identifiers need to be assigned to their
           names. Generally, the names coming from the parses are registered here.
        */
        func_decl * try_get_predicate_decl(symbol const& pred_name) const {
            func_decl * res = 0;
            m_preds_by_name.find(pred_name, res);
            return res;
        }        

        /**
           \brief Create a fresh head predicate declaration.

        */
        func_decl * mk_fresh_head_predicate(symbol const & prefix, symbol const & suffix, 
            unsigned arity, sort * const * domain, func_decl* orig_pred=0);


        /**
           \brief Return number of a symbol in a DK_SYMBOL kind sort (\see register_sort() )
         */
        finite_element get_constant_number(relation_sort sort, symbol s);
        /**
           \brief Return number of a symbol in a DK_UINT64 kind sort (\see register_sort() )
         */
        finite_element get_constant_number(relation_sort srt, uint64 el);

        /**
           \brief Output name of constant with number \c num in sort \c sort.
        */
        void print_constant_name(relation_sort sort, uint64 num, std::ostream & out);

        bool try_get_sort_constant_count(relation_sort srt, uint64 & constant_count);

        uint64 get_sort_size_estimate(relation_sort srt);

        /**
           \brief Assign names of variables used in the declaration of a predicate.

           These names are used when printing out the relations to make the output conform 
           to the one of bddbddb.
        */
        void set_argument_names(const func_decl * pred, svector<symbol> var_names);
        symbol get_argument_name(const func_decl * pred, unsigned arg_index);

        void set_predicate_representation(func_decl * pred, unsigned relation_name_cnt, 
            symbol const *  relation_names);

        void set_output_predicate(func_decl * pred) { m_rule_set.set_output_predicate(pred); }

        rule_set & get_rules() { flush_add_rules(); return m_rule_set; }

        void get_rules_as_formulas(expr_ref_vector& fmls, svector<symbol>& names);

        void add_fact(app * head);
        void add_fact(func_decl * pred, const relation_fact & fact);

        bool has_facts(func_decl * pred) const;
        
        void add_rule(rule_ref& r);
        
        void assert_expr(expr* e);
        expr_ref get_background_assertion();
        unsigned get_num_assertions() { return m_background.size(); }
        expr*    get_assertion(unsigned i) const { return m_background[i]; }

        /**
           Method exposed from API for adding rules.
        */
        void add_rule(expr* rl, symbol const& name);
        

        /**
           Update a named rule.
         */
        void update_rule(expr* rl, symbol const& name);

        /**
           Retrieve the maximal number of relevant unfoldings of 'pred'
           with respect to the current state.
         */
        unsigned get_num_levels(func_decl* pred);

        /**
           Retrieve the current cover of 'pred' up to 'level' unfoldings.
           Return just the delta that is known at 'level'. To
           obtain the full set of properties of 'pred' one should query
           at 'level+1', 'level+2' etc, and include level=-1.
        */
        expr_ref get_cover_delta(int level, func_decl* pred);
       
        /**
           Add a property of predicate 'pred' at 'level'. 
           It gets pushed forward when possible.
         */
        void add_cover(int level, func_decl* pred, expr* property);

        /**
           \brief Check rule subsumption.
        */
        bool check_subsumes(rule const& stronger_rule, rule const& weaker_rule);

        /**
          \brief Check if rule is well-formed according to engine.
        */
        void check_rule(rule_ref& r);

        /**
           \brief Return true if facts to \c pred can be added using the \c add_table_fact() function.

           This function should return true if \c pred is represented by a table_relation
           and there is no transformation of relation values before they are put into the
           table.
         */
        void add_table_fact(func_decl * pred, const table_fact & fact);
        void add_table_fact(func_decl * pred, unsigned num_args, unsigned args[]);

        /**
           \brief To be called after all rules are added.
        */
        void close();
        void ensure_closed();
        bool is_closed() { return m_closed; }

        /**
           \brief Undo the effect of the \c close operation.
         */
        void reopen();
        void ensure_opened();

        model_converter_ref& get_model_converter() { return m_mc; }
        void add_model_converter(model_converter* mc) { m_mc = concat(m_mc.get(), mc); }
        proof_converter_ref& get_proof_converter() { return m_pc; }
        void add_proof_converter(proof_converter* pc) { m_pc = concat(m_pc.get(), pc); }

        void transform_rules(); 
        void transform_rules(rule_transformer& transf); 
        void transform_rules(rule_transformer::plugin* plugin);
        void replace_rules(rule_set const& rs);
        void record_transformed_rules();

        void apply_default_transformation(); 

        void collect_params(param_descrs& r);
        
        void updt_params(params_ref const& p);

        void display_rules(std::ostream & out) const {
            m_rule_set.display(out);
        }

        void display(std::ostream & out) const {
            display_rules(out);
            if (m_rel) m_rel->display_facts(out);
        }

        void display_smt2(unsigned num_queries, expr* const* queries, std::ostream& out);

        void display_profile(std::ostream& out) const;

        // -----------------------------------
        //
        // basic usage methods
        //
        // -----------------------------------

        void cancel();
        bool canceled() const { return m_cancel; }

        void cleanup();
        void reset_cancel() { cleanup(); }

        /**
           \brief check if query 'q' is satisfied under asserted rules and background.

           If successful, return OK and into \c result assign a relation with all 
           tuples matching the query. Otherwise return reason for failure and do not modify
           \c result.

           The numbers of variables in the query body must form a contiguous sequence
           starting from zero.

           The caller becomes an owner of the relation object returned in \c result. The
           relation object, however, should not outlive the datalog context since it is 
           linked to a relation plugin in the context.
         */

        lbool query(expr* q);

        /**
           \brief retrieve model from inductive invariant that shows query is unsat.
           
           \pre engine == 'pdr' - this option is only supported for PDR mode.
         */
        model_ref get_model();

        /**
           \brief retrieve proof from derivation of the query.
           
           \pre engine == 'pdr' - this option is only supported for PDR mode.
         */
        proof_ref get_proof();


        /**
           Query multiple output relations.
        */
        lbool rel_query(unsigned num_rels, func_decl * const* rels);


        /**
           \brief retrieve last proof status.
        */
        execution_result get_status();

        void set_status(execution_result r) { m_last_status = r; }

        /**
           \brief retrieve formula corresponding to query that returns l_true.
           The formula describes one or more instances of the existential variables
           in the query that are derivable.
        */
        expr* get_answer_as_formula();


        void collect_statistics(statistics& st) const;

        void reset_statistics();

        /**
           \brief Display a certificate for reachability and/or unreachability.
        */
        void display_certificate(std::ostream& out);

        /**
           \brief query result if it contains fact.
         */
        bool result_contains_fact(relation_fact const& f);

        rel_context* get_rel_context() { ensure_engine(); return m_rel; }

    private:

        /**
           Just reset all tables.
        */
        void reset_tables(); 


        void flush_add_rules();

        void ensure_engine();

        void check_quantifier_free(rule_ref& r);        
        void check_uninterpreted_free(rule_ref& r);
        void check_existential_tail(rule_ref& r);
        void check_positive_predicates(rule_ref& r);

        // auxilary functions for SMT2 pretty-printer.
        void declare_vars(expr_ref_vector& rules, mk_fresh_name& mk_fresh, std::ostream& out);

        //undefined and private copy constructor and operator=
        context(const context&);
        context& operator=(const context&);
    };

};

#endif /* _DL_CONTEXT_H_ */

