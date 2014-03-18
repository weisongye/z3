/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    predabst_context.cpp

Abstract:

    Bounded PREDABST (symbolic simulation using Z3) context.

Author:

    Nikolaj Bjorner (nbjorner) 2013-04-26

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
        //        std::string            m_pred_symbol_prefix; // TBD replace by proper constant
        static char const * const m_pred_symbol_prefix; // prefix for predicate containing rules
        static unsigned const m_pred_symbol_prefix_size; // prefix for predicate containing rules

        typedef obj_map<func_decl, ptr_vector<app>> pred_abst_map;

        pred_abst_map           m_pred_abst_map; // map from predicate declarations to predicates

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
            //            m_pred_symbol_prefix("__pred__")
        {
            // m_fparams.m_relevancy_lvl = 0;
            m_fparams.m_mbqi = false;
            m_fparams.m_soft_timeout = 1000;
        }

        ~imp() {}        

        lbool query(expr* query) {
            m_ctx.ensure_opened();

            datalog::rule_set & rules = m_ctx.get_rules();

            // collect predicate definitions
            for (rule_set::iterator it = rules.begin(); it != rules.end(); ++it) {
                rule * r = *it;
                char const * head_str = r->get_decl()->get_name().bare_str();
                if (r->get_uninterpreted_tail_size() == 0 
                    && !memcmp(head_str, m_pred_symbol_prefix, m_pred_symbol_prefix_size)
                    ) {
                    unsigned suffix_size = strlen(head_str)-m_pred_symbol_prefix_size;
                    char * suffix = new char[suffix_size+1];
                    strcpy_s(suffix, suffix_size+1, &head_str[m_pred_symbol_prefix_size]);
                    ptr_vector<app> preds;
                    for (unsigned i = 0; i < r->get_tail_size(); ++i)  {
                        preds.push_back(r->get_tail(i));
                    }
                    func_decl * d = r->get_decl();
                    m_pred_abst_map.insert(m.mk_func_decl(symbol(suffix), d->get_arity(), d->get_domain(), d->get_range()), preds);
                    rules.del_rule(r);
                }
            }

            for (pred_abst_map::iterator it = m_pred_abst_map.begin(); it != m_pred_abst_map.end(); ++it) {
                std::cout << "preds:: key " << mk_pp(it->m_key, m) << std::endl;
                ptr_vector<app> preds = it->m_value;
                for (ptr_vector<app>::iterator it2 = preds.begin(); it2 != preds.end(); ++it2) {
                    app * pred = *it2;
                    std::cout << mk_pp(pred, m) << " ";
                }
                std::cout << std::endl;
            }

            std::cout << "remaining rules "<< rules.get_num_rules() << std::endl;
            rules.display(std::cout);
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
