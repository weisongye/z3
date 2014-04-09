/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    predabst_context.cpp

Abstract:

    Bounded PREDABST (symbolic simulation using Z3) context.

Author:

    Nikolaj Bjorner (nbjorner) 2013-04-26
    Modified by Andrey Rybalchenko (rybal) 2014-3-7.

Revision History:

--*/

#include "predabst_context.h"
#include "dl_context.h"
#include "unifier.h"
#include "var_subst.h"
#include "substitution.h"
#include "smt_kernel.h"
#include "dl_transforms.h"

#include <cstring>

namespace datalog {

    class predabst::imp {
        struct stats {
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
            unsigned m_num_unfold;
            unsigned m_num_no_unfold;
            unsigned m_num_subsumed;
        };

        context&               m_ctx;         // main context where (fixedpoint) constraints are stored.
        ast_manager&           m;             // manager for ASTs. It is used for managing expressions
        rule_manager&          rm;            // context with utilities for fixedpoint rules.
        smt_params             m_fparams;     // parameters specific to smt solving
        smt::kernel            m_solver;      // basic SMT solver class
        var_subst              m_var_subst;   // substitution object. It gets updated and reset.
        expr_ref_vector        m_ground;      // vector of ground formulas during a search branch.
        app_ref_vector         m_goals;       // vector of recursive predicates in the SLD resolution tree.
        volatile bool          m_cancel;      // Boolean flag to track external cancelation.
        stats                  m_stats;       // statistics information specific to the CLP module.

        static char const * const m_pred_symbol_prefix; // prefix for predicate containing rules
        static unsigned const  m_pred_symbol_prefix_size; // prefix for predicate containing rules

        typedef obj_map<func_decl, unsigned> func_decl2occur_count;
        func_decl2occur_count  m_func_decl2occur_count;

        typedef svector<std::pair<expr_ref_vector *, expr_ref_vector *>> ssa_subst_preds_pairs;
        ssa_subst_preds_pairs m_empty_ssa_subst_preds_pairs;
        typedef obj_map<func_decl, ssa_subst_preds_pairs> func_decl2ssa_subst_preds_pairs;
        func_decl2ssa_subst_preds_pairs m_func_decl2ssa_subst_preds_pairs;

        typedef obj_map<rule, expr *> rule2ground_body;
        rule2ground_body m_rule2ground_body;

    public:
        imp(context& ctx):
            m_ctx(ctx), 
            m(ctx.get_manager()),
            rm(ctx.get_rule_manager()),
            m_solver(m, m_fparams),  
            m_var_subst(m, false),
            m_ground(m),
            m_goals(m),
            m_cancel(false)
        {
            // m_fparams.m_relevancy_lvl = 0;
            m_fparams.m_mbqi = false;
            m_fparams.m_soft_timeout = 1000;
        }

        ~imp() {
            for (func_decl2ssa_subst_preds_pairs::iterator it = m_func_decl2ssa_subst_preds_pairs.begin();
                 it != m_func_decl2ssa_subst_preds_pairs.end(); ++it) 
                for (ssa_subst_preds_pairs::iterator it2 = it->m_value.begin(); it2 != it->m_value.end(); ++it2) {
                    dealloc(it2->first);
                    dealloc(it2->second);
                }
            std::cout << "end ~imp" << std::endl;
        }        

        lbool query(expr* query) {
            m_ctx.ensure_opened();

            datalog::rule_set & rules = m_ctx.get_rules();

            std::cout << "begin original rules\n";
            rules.display(std::cout);
            std::cout << "end original rules\n";

            // update func_decl counters
            // collect predicates and delete corresponding rules
            for (rule_set::iterator it = rules.begin(); it != rules.end(); ++it) {
                rule * r = *it;
                func_decl * head_decl = r->get_decl();
                char const * head_str = head_decl->get_name().bare_str();
                std::cout << "---------------------------------------\n";
                std::cout << " here -1: " << r->get_uninterpreted_tail_size() << std::endl;
                r->display(m_ctx, std::cout);

                if (r->get_uninterpreted_tail_size() != 0 
                    || memcmp(head_str, m_pred_symbol_prefix, m_pred_symbol_prefix_size)
                    ) {
                    std::cout << " here0: " << r->get_uninterpreted_tail_size() << std::endl;
                    r->display(m_ctx, std::cout);
                    for (unsigned i = 0; i < r->get_uninterpreted_tail_size(); ++i) {
                        std::cout << " here1 \n";
                        func_decl2occur_count::obj_map_entry * e = m_func_decl2occur_count.find_core(r->get_decl(i));
                        if (e) {
                            e->get_data().m_value = e->get_data().m_value+1;
                        } else {
                            m_func_decl2occur_count.insert(r->get_decl(i), 1);
                        }
                    }
                    continue;
                }
                // create func_decl from suffix and map it to predicates
                unsigned suffix_size = strlen(head_str)-m_pred_symbol_prefix_size;
                char * suffix = new char[suffix_size+1];
#ifdef _WINDOWS
		strcpy_s(suffix, suffix_size+1, &head_str[m_pred_symbol_prefix_size]); // not yet available outside Windows
#else
                strncpy(suffix, &head_str[m_pred_symbol_prefix_size], suffix_size+1);
#endif
                // prepare grounding constants
                expr_ref_vector * subst = alloc(expr_ref_vector, m); 
                unsigned head_arity = head_decl->get_arity();
                subst->reserve(head_arity);
                for (unsigned i = 0; i < head_arity; ++i) 
                    (*subst)[i] = m.mk_fresh_const("c", head_decl->get_domain(i));
                // ground predicates
                expr_ref_vector * ground_preds = alloc(expr_ref_vector, m); 
                ground_preds->reserve(r->get_tail_size());
                expr_ref ground_pred(m);
                for (unsigned i = 0; i < r->get_tail_size(); ++i) {
                    m_var_subst(r->get_tail(i), head_arity, subst->c_ptr(), ground_pred);
                    (*ground_preds)[i] = ground_pred; 
                }
                // store in ssa-ish vector and then into map
                ssa_subst_preds_pairs subst_preds0; 
                subst_preds0.push_back(std::make_pair(subst, ground_preds));
                m_func_decl2ssa_subst_preds_pairs.insert(m.mk_func_decl(symbol(suffix), head_arity, head_decl->get_domain(), head_decl->get_range()),
                                                         subst_preds0); 
                // corresponding rule is not used for inference
                rules.del_rule(r);
            }

            // print func_decl occurence counters
            std::cout << "func_decl occurence counts:" << std::endl;
            for (func_decl2occur_count::iterator it = m_func_decl2occur_count.begin(); it != m_func_decl2occur_count.end(); ++it) 
                std::cout << mk_pp(it->m_key, m) << " " << it->m_value << std::endl;

            // print collected predicates
            for (func_decl2ssa_subst_preds_pairs::iterator it = m_func_decl2ssa_subst_preds_pairs.begin();
                 it != m_func_decl2ssa_subst_preds_pairs.end(); ++it) {
                std::cout << "preds " << mk_pp(it->m_key, m) << ":";
                for (ssa_subst_preds_pairs::iterator it2 = it->m_value.begin(); it2 != it->m_value.end(); ++it2) 
                    for (expr_ref_vector::iterator it3 = it2->second->begin(); it3 != it2->second->end(); ++it3) 
                        std::cout << " " << mk_pp(*it3, m);
                std::cout << std::endl;
            }

            std::cout << "remaining rules "<< rules.get_num_rules() << std::endl;
            rules.display(std::cout);

            // simulate initial abstract step
            /*
            for (rule_set::iterator it = rules.begin(); it != rules.end(); ++it) {
                rule * r = *it;
                if (r->get_uninterpreted_tail_size() != 0) continue;
                app * head = r->get_head();
                std::cout << "rule head " << mk_pp(head, m) << std::endl;
                pred_abst_map::obj_map_entry * e = m_pred_abst_map.find_core(head->get_decl());
                expr_ref_vector const & preds = e ? *e->get_data().get_value() : m_empty_preds;
                std::cout << "found preds " << preds.size() << std::endl;
                if (preds.size() == 0) {
                    std::cout << "abstraction is true" << std::endl;
                    continue;
                }
                // ground head
  
//                expr_ref_vector m_ground(m);
//                unsigned arity = head->get_num_args();
//                m_ground.reserve(arity);
//                for (unsigned i = 0; i < arity; ++i) {
//                    m_ground[i] = m.mk_fresh_const("c", head->get_decl()->get_domain(i));
//                }
//                expr_ref tmp(head, m);
//                m_var_subst(head, m_ground.size(), m_ground.c_ptr(), tmp); // NOT NEEDED!

//                std::cout << "after subst " << mk_pp(tmp, m) << std::endl;
//                m_var_subst.reset();
//                std::cout << std::endl;

            }
            */
            return l_true;
        }
           
    
        void cancel() {
            m_cancel = true;
            m_solver.cancel();
        }
        
        void cleanup() {
            m_cancel = false;
            // TBD hmm?
            m_goals.reset();
            m_solver.reset_cancel();
        }

        void reset_statistics() {
            m_stats.reset();
        }

        void collect_statistics(statistics& st) const {
            // TBD hmm?
        }

        void display_certificate(std::ostream& out) const {
            // TBD hmm?
            expr_ref ans = get_answer();
            out << mk_pp(ans, m) << "\n";    
        }

        expr_ref get_answer() const {
            // TBD hmm?
            return expr_ref(m.mk_true(), m);
        }

    private:

        bool is_pred_def_rule(rule const & r) {
            return true;
        }

    };

    char const * const predabst::imp::m_pred_symbol_prefix = "__pred__";
    unsigned const predabst::imp::m_pred_symbol_prefix_size = strlen(m_pred_symbol_prefix);
    
    predabst::predabst(context& ctx):
        engine_base(ctx.get_manager(), "predabst"),
        m_imp(alloc(imp, ctx)) {        
    }
    predabst::~predabst() {
        dealloc(m_imp);
    }    
    lbool predabst::query(expr* query) {
        return m_imp->query(query);
    }
    void predabst::cancel() {
        m_imp->cancel();
    }
    void predabst::cleanup() {
        m_imp->cleanup();
    }
    void predabst::reset_statistics() {
        m_imp->reset_statistics();
    }
    void predabst::collect_statistics(statistics& st) const {
        m_imp->collect_statistics(st);
    }
    void predabst::display_certificate(std::ostream& out) const {
        m_imp->display_certificate(out);
    }
    expr_ref predabst::get_answer() {
        return m_imp->get_answer();
    }

};
