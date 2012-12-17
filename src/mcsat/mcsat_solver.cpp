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
#include"mcsat_solver.h"
#include"mcsat_preprocessor.h"
#include"mcsat_kernel.h"
#include"mcsat_plugin.h"
#include"tactic.h"
#include"params.h"
#include"scoped_ptr_vector.h"

namespace mcsat {

    class solver : public ::solver {
        ast_manager & m_manager;
        preprocessor  m_preprocessor;
        kernel        m_kernel;

        friend class solver_factory;
        
    public:
        solver(ast_manager & m, params_ref const & p, bool produce_proofs, bool produce_models, bool produce_unsat_cores):
            m_manager(m),
            m_preprocessor(m, produce_proofs, produce_models, produce_unsat_cores),
            m_kernel(m, produce_proofs) {
        }

        ast_manager & m() const {
            return m_manager;
        }
        
        virtual ~solver() {
        }

        virtual void collect_param_descrs(param_descrs & r) {
            // do nothing
        }

        virtual void set_produce_models(bool f) {
            // do nothing, mcsat always produce models.
        }

        virtual void set_progress_callback(progress_callback * callback) {
            // TODO
        }
       
        virtual void updt_params(params_ref const & p) {
        }
        
        virtual void set_cancel(bool f) {
            m_preprocessor.set_cancel(f);
        }
        
        virtual unsigned get_num_assertions() const {
            return m_preprocessor.size();
        }
        
        virtual expr * get_assertion(unsigned idx) const {
            return m_preprocessor.form(idx);
        }
        
        virtual void display(std::ostream & out) const {
            m_preprocessor.display(out);
        }

        virtual unsigned get_scope_level() const {
            return m_preprocessor.scope_lvl();
        }

        virtual void push() {
            m_preprocessor.push();
            m_kernel.push();
        }
        
        virtual void pop(unsigned n) {
            m_preprocessor.pop(n);
            m_kernel.pop(n);
        }
        
        virtual void assert_expr(expr * t, expr * a) {
            proof * pr = m_preprocessor.proofs_enabled() ? m().mk_asserted(t) : 0;
            expr_dependency * dep = (a && m_preprocessor.unsat_core_enabled()) ? m().mk_leaf(a) : 0;
            m_preprocessor.assert_expr(t, pr, dep);
        }
        
        virtual void assert_expr(expr * t) {
            proof * pr = m_preprocessor.proofs_enabled() ? m().mk_asserted(t) : 0;
            m_preprocessor.assert_expr(t, pr, 0);
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
    };

    struct solver_factory::imp {
        scoped_ptr_vector<tactic_factory> m_before_tactics;
        scoped_ptr_vector<tactic_factory> m_after_tactics;
        plugin_ref_vector                 m_plugins;
    };
    
    solver_factory::solver_factory() {
        m_imp = alloc(imp);
    }
    
    solver_factory::~solver_factory() {
        dealloc(m_imp);
    }
    
    void solver_factory::add_tactic_before(tactic_factory * f) {
        m_imp->m_before_tactics.push_back(f);
    }
    
    void solver_factory::add_tactic_after(tactic_factory * f) {
        m_imp->m_after_tactics.push_back(f);
    }

    void solver_factory::add_plugin(plugin * p) {
        m_imp->m_plugins.push_back(p);
    }
    
    ::solver * solver_factory::operator()(ast_manager & m, params_ref const & p, bool proofs_enabled, bool models_enabled, bool unsat_core_enabled, symbol const & logic) {
        solver * r = alloc(solver, m, p, proofs_enabled, models_enabled, unsat_core_enabled);
        unsigned sz = m_imp->m_before_tactics.size();
        for (unsigned i = 0; i < sz; i++) {
            tactic_factory & f = *(m_imp->m_before_tactics[i]);
            r->m_preprocessor.add_tactic_before(f(m, p));
        }
        sz = m_imp->m_after_tactics.size();
        for (unsigned i = 0; i < sz; i++) {
            tactic_factory & f = *(m_imp->m_after_tactics[i]);
            r->m_preprocessor.add_tactic_after(f(m, p));
        }

        sz = m_imp->m_plugins.size();
        for (unsigned i = 0; i < sz; i++) {
            r->m_kernel.add_plugin(m_imp->m_plugins.get(i));
        }
        return r;
    }

};

