/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_solver.h

Abstract:

    MCSAT solver.

Author:

    Leonardo de Moura (leonardo) 2012-11-01.

Revision History:

--*/
#include"solver.h"
#include"mcsat_preprocessor.h"
#include"mcsat_kernel.h"
#include"params.h"

namespace mcsat {

    class solver : public ::solver {
        
        struct imp {
            ast_manager & m_manager;
            preprocessor  m_preprocessor;
            // kernel        m_kernel;
            
            imp(ast_manager & m, bool produce_proofs, bool produce_models, bool produce_unsat_cores, params_ref const & p):
                m_manager(m),
                m_preprocessor(m, produce_proofs, produce_models, produce_unsat_cores) {
            }
                
            ast_manager & m() const {
                return m_manager;
            }
            
            void updt_params(params_ref const & p) {
            }
            
            void set_cancel(bool f) {
                m_preprocessor.set_cancel(f);
            }

            void assert_expr(expr * t, expr * a) {
                proof * pr = m_preprocessor.proofs_enabled() ? m().mk_asserted(t) : 0;
                expr_dependency * dep = (a && m_preprocessor.unsat_core_enabled()) ? m().mk_leaf(a) : 0;
                m_preprocessor.assert_expr(t, pr, dep);
            }

            void assert_expr(expr * t) {
                proof * pr = m_preprocessor.proofs_enabled() ? m().mk_asserted(t) : 0;
                m_preprocessor.assert_expr(t, pr, 0);
            }

            void push() {
                m_preprocessor.push();
            }

            void pop(unsigned n) {
                m_preprocessor.pop(n);
            }
            
            unsigned get_scope_level() const {
                return m_preprocessor.scope_lvl();
            }

            void display(std::ostream & out) const {
                m_preprocessor.display(out);
            }
        };

        ast_manager * m_manager;
        bool          m_produce_models;
        bool          m_produce_proofs;
        bool          m_produce_unsat_cores;
        params_ref    m_params;
        imp *         m_imp;
        
        imp & get_imp() {
            SASSERT(m_manager);
            if (!m_imp) {
                #pragma omp critical (mcsat_solver)
                {
                    m_imp = alloc(imp, *m_manager, m_produce_proofs, m_produce_models, m_produce_unsat_cores, m_params);
                }
            }
            return *m_imp;
        }

    public:
        solver():
            m_manager(0),
            m_produce_models(true),
            m_produce_proofs(false),
            m_produce_unsat_cores(false),
            m_imp(0) {
        }

        ~solver() {
            if (m_imp) 
                dealloc(m_imp);
        }
        
        virtual void updt_params(params_ref const & p) {
            m_params = p;
            if (m_imp)
                m_imp->updt_params(p);
        }
        
        virtual void collect_param_descrs(param_descrs & r) {
            // do nothing
        }
        
        virtual void set_produce_proofs(bool f) {
            m_produce_proofs = f;
        }

        virtual void set_produce_models(bool f) {
            m_produce_models = f;
        }

        virtual void set_produce_unsat_cores(bool f) {
            m_produce_unsat_cores = f;
        }
        
        virtual void init(ast_manager & m, symbol const & logic) {
            m_manager = &m;
        }

        virtual void reset() {
            if (m_imp) {
                #pragma omp critical (mcsat_solver)
                {
                    dealloc(m_imp);
                    m_imp = 0;
                }
            }
        }
        
        virtual void assert_expr(expr * t, expr * a) {
            get_imp().assert_expr(t, a);
        }

        virtual void assert_expr(expr * t) {
            get_imp().assert_expr(t);
        }

        virtual void push() {
            get_imp().push();
        }

        virtual void pop(unsigned n) {
            get_imp().pop(n);
        }

        virtual unsigned get_scope_level() const {
            if (m_imp)
                return m_imp->get_scope_level();
            else
                return 0;
        }

        virtual lbool check_sat(unsigned num_assumptions, expr * const * assumptions) {
            // TODO
            return l_undef;
        }

        virtual void collect_statistics(statistics & st) const {
            // TODO
        }

        virtual void get_unsat_core(ptr_vector<expr> & r) {
            // TODO
        }

        virtual void get_model(model_ref & m) {
            // TODO
        }

        virtual proof * get_proof() {
            NOT_IMPLEMENTED_YET();
        }

        virtual std::string reason_unknown() const {
            return "unknown";
        }

        virtual void get_labels(svector<symbol> & r) {
            throw default_exception("mcsat does not support get_labels");
        }

        virtual void set_cancel(bool f) {
            #pragma omp critical (mcsat_solver)
            {
                if (m_imp) {
                    m_imp->set_cancel(f);
                }
            }
        }

        virtual void set_progress_callback(progress_callback * callback) {
            // TODO
        }

        virtual unsigned get_num_assertions() const {
            if (m_imp)
                return m_imp->m_preprocessor.size();
            else
                return 0;
        }
        
        virtual expr * get_assertion(unsigned idx) const {
            SASSERT(idx < get_num_assertions());
            SASSERT(m_imp);
            return m_imp->m_preprocessor.form(idx);
        }

        virtual void display(std::ostream & out) const {
            if (m_imp)
                m_imp->display(out);
            else
                out << "(solver)";
        }
    };
};

solver * mk_mcsat_solver() {
    return alloc(mcsat::solver);
}
