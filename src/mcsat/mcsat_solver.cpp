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

namespace mcsat {

    struct solver::imp {
        ast_manager & m_manager;
        params_ref    m_params;
        // preprocessor  m_preprocessor;
        // kernel        m_kernel;

        imp(ast_manager & m):
            m_manager(m) {
            TRACE("mcsat", tout << "initializing mcsat solver.\n";);
        }

        ast_manager & m() const {
            return m_manager;
        }

        void updt_params(params_ref const & p) {
            m_params = p;
        }

        void set_cancel(bool f) {
        }
    };

    solver::solver():
        m_imp(0) {
    }
    
    solver::~solver() {
        if (m_imp)
            dealloc(m_imp);
    }

    void solver::updt_params(params_ref const & p) {
        SASSERT(m_imp);
        m_imp->updt_params(p);
    }

    void solver::collect_param_descrs(param_descrs & r) {
    }
        
    void solver::set_produce_proofs(bool f) {
        // NOOP
        // proof production must be enabled using updt_params
    }

    void solver::set_produce_models(bool f) {
        // NOOP
        // model construction is always enabled for mcsat
    }

    void solver::set_produce_unsat_cores(bool f) {
        // NOOP
        // unsat-core generation must be enabled uisng updt_params
    }

    void solver::init(ast_manager & m, symbol const & logic) {
        #pragma omp critical (mcsat_solver)
        {
            if (m_imp) {
                dealloc(m_imp);
                m_imp = 0;
            }
            m_imp = alloc(imp, m);
        }
    }

    void solver::reset() {
        if (!m_imp)
            return;
        ast_manager & m = m_imp->m();
        params_ref p    = m_imp->m_params;
        symbol logic("unknown");
        init(m, logic);
        m_imp->updt_params(p);
    }

    void solver::assert_expr(expr * t) {
    }

    void solver::assert_expr(expr * t, expr * a) {
    }

    void solver::push() {
    }

    void solver::pop(unsigned n) {
    }
    
    unsigned solver::get_scope_level() const {
        return 0;
    }

    lbool solver::check_sat(unsigned num_assumptions, expr * const * assumptions) {
        return l_undef;
    }

    void solver::collect_statistics(statistics & st) const {
    }

    void solver::get_unsat_core(ptr_vector<expr> & r) {
    }

    void solver::get_model(model_ref & m) {
    }

    proof * solver::get_proof() {
        return 0;
    }

    std::string solver::reason_unknown() const {
        return "unknown";
    }

    void solver::get_labels(svector<symbol> & r) {
    }

    void solver::set_cancel(bool f) {
      #pragma omp critical (mcsat_solver)
      {
          if (m_imp)
              m_imp->set_cancel(f);
      }
    }

    void solver::set_progress_callback(progress_callback * callback) {
    }

    unsigned solver::get_num_assertions() const {
        return 0;
    }

    expr * solver::get_assertion(unsigned idx) const {
        return 0;
    }

    void solver::display(std::ostream & out) const {
    }

};
