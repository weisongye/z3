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
        static unsigned const m_pred_symbol_prefix_size; // prefix for predicate containing rules

        typedef expr_ref_vector pred_vector;
        typedef obj_map<func_decl, pred_vector *> pred_abst_map;

        pred_abst_map           m_pred_abst_map; // map from predicate declarations to predicates
        pred_vector         m_empty_preds;  // empty vector predicates 
    public:
        imp(context& ctx):
            m_ctx(ctx), 
            m(ctx.get_manager()),
            rm(ctx.get_rule_manager()),
            m_solver(m, m_fparams),  
            m_var_subst(m, false),
            m_ground(m),
            m_goals(m),
            m_cancel(false),
            m_empty_preds(m)
        {
            // m_fparams.m_relevancy_lvl = 0;
            m_fparams.m_mbqi = false;
            m_fparams.m_soft_timeout = 1000;
        }

        ~imp() {
            for (pred_abst_map::iterator it = m_pred_abst_map.begin(); it != m_pred_abst_map.end(); ++it) {
                dealloc(it->m_value);
            }
        }        

        lbool query(expr* query) {
            m_ctx.ensure_opened();

            datalog::rule_set & rules = m_ctx.get_rules();

            // collect predicates and delete corresponding rules
            for (rule_set::iterator it = rules.begin(); it != rules.end(); ++it) {
                rule * r = *it;
                func_decl * head_decl = r->get_decl();
                char const * head_str = head_decl->get_name().bare_str();
                if (r->get_uninterpreted_tail_size() != 0 
                    || memcmp(head_str, m_pred_symbol_prefix, m_pred_symbol_prefix_size)
                    ) continue;

                // grounding
                pred_vector m_ground(m); // TODO pointer to heap allocated object
                unsigned arity = head_decl->get_arity();
                m_ground.reserve(arity);
                for (unsigned i = 0; i < arity; ++i) {
                    m_ground[i] = m.mk_fresh_const("c", head_decl->get_domain(i));
                }

                // ground predicates
                pred_vector * preds = alloc(pred_vector, m); 
                expr_ref tmp(m);
                for (unsigned i = 0; i < r->get_tail_size(); ++i)  {
                    m_var_subst(r->get_tail(i), arity, m_ground.c_ptr(), tmp);
                    preds->push_back(tmp); // TODO who destructs this pointer?
                }

                // create func_decl from suffix and map it to predicates
                unsigned suffix_size = strlen(head_str)-m_pred_symbol_prefix_size;
                char * suffix = new char[suffix_size+1];
#ifdef _WINDOWS
		strcpy_s(suffix, suffix_size+1, &head_str[m_pred_symbol_prefix_size]); // not yet available outside Windows
#else
                strncpy(suffix, &head_str[m_pred_symbol_prefix_size], suffix_size+1);
#endif
                func_decl * d = r->get_decl();
                m_pred_abst_map.insert(m.mk_func_decl(symbol(suffix), d->get_arity(), d->get_domain(), d->get_range()), preds);
                // corresponding rule is not used for inference
                rules.del_rule(r);
            }

            // print collected predicates
            for (pred_abst_map::iterator it = m_pred_abst_map.begin(); it != m_pred_abst_map.end(); ++it) {
                std::cout << "preds" << mk_pp(it->m_key, m) << std::endl;
                pred_vector * preds = it->m_value;

                for (pred_vector::iterator it2 = preds->begin(); it2 != preds->end(); ++it2) {
                    std::cout << " " << mk_pp(*it2, m);
                }
                std::cout << std::endl;
            }

            std::cout << "remaining rules "<< rules.get_num_rules() << std::endl;
            rules.display(std::cout);

            // simulate initial abstract step
            for (rule_set::iterator it = rules.begin(); it != rules.end(); ++it) {
                rule * r = *it;
                if (r->get_uninterpreted_tail_size() != 0) continue;
                app * head = r->get_head();
                std::cout << "rule head " << mk_pp(head, m) << "/" << head->get_num_args() << head->get_decl()->get_arity() << std::endl;
                pred_abst_map::obj_map_entry * e = m_pred_abst_map.find_core(head->get_decl());
                pred_vector const & preds = e ? *e->get_data().m_value : m_empty_preds;
                std::cout << "found preds " << preds.size() << std::endl;
                /*
                std::cout << "sorts:";
                expr_ref_vector m_ground(m);
                unsigned arity = head->get_num_args();
                m_ground.reserve(arity);
                for (unsigned i = 0; i < arity; ++i) {
                    std::cout << " " << mk_pp(head->get_decl()->get_domain(i), m);
                    m_ground[i] = m.mk_fresh_const("c", head->get_decl()->get_domain(i));
                }
                expr_ref tmp(head, m);
                m_var_subst(head, m_ground.size(), m_ground.c_ptr(), tmp);

                std::cout << "after subst " << mk_pp(tmp, m) << std::endl;
                m_var_subst.reset();
                std::cout << std::endl;
                */
            }

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
