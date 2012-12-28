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
#include"mcsat_exception.h"
#include"tactic.h"
#include"params.h"
#include"scoped_ptr_vector.h"

namespace mcsat {

    solver::solver(ast_manager & m, params_ref const & p, bool produce_proofs, bool produce_models, bool produce_unsat_cores):
        m_manager(m) {
        m_preprocessor = alloc(preprocessor, m, produce_proofs, produce_models, produce_unsat_cores);
        m_kernel       = alloc(kernel, m, produce_proofs);
    }

    ast_manager & solver::m() const {
        return m_manager;
    }
    
    solver::~solver() {
    }
    
    void solver::collect_param_descrs(param_descrs & r) {
        // do nothing
    }
    
    void solver::set_produce_models(bool f) {
        // do nothing, mcsat always produce models.
    }
    
    void solver::set_progress_callback(progress_callback * callback) {
        // TODO
    }
    
    void solver::updt_params(params_ref const & p) {
    }
    
    void solver::set_cancel(bool f) {
        m_preprocessor->set_cancel(f);
        m_kernel->set_cancel(f);
    }
        
    unsigned solver::get_num_assertions() const {
        return m_preprocessor->size();
    }
    
    expr * solver::get_assertion(unsigned idx) const {
        return m_preprocessor->form(idx);
    }
        
    void solver::display(std::ostream & out) const {
        m_preprocessor->display(out);
    }
    
    unsigned solver::get_scope_level() const {
        return m_preprocessor->scope_lvl();
    }
    
    void solver::commit() {
        unsigned qhead = m_preprocessor->qhead();
        m_preprocessor->commit();
        if (!m_preprocessor->inconsistent()) {
            unsigned sz    = m_preprocessor->size();
            for (unsigned i = qhead; i < sz; i++) {
                m_kernel->assert_expr(m_preprocessor->form(i), m_preprocessor->pr(i), m_preprocessor->dep(i));
            }
        }
    }
    
    void solver::push() {
        commit();
        m_preprocessor->push();
        m_kernel->push();
    }
    
    void solver::pop(unsigned n) {
        m_preprocessor->pop(n);
        m_kernel->pop(n);
    }
    
    void solver::assert_expr(expr * t, expr * a) {
        proof * pr = m_preprocessor->proofs_enabled() ? m().mk_asserted(t) : 0;
        expr_dependency * dep = (a && m_preprocessor->unsat_core_enabled()) ? m().mk_leaf(a) : 0;
        m_preprocessor->assert_expr(t, pr, dep);
    }
    
    void solver::assert_expr(expr * t) {
        proof * pr = m_preprocessor->proofs_enabled() ? m().mk_asserted(t) : 0;
        m_preprocessor->assert_expr(t, pr, 0);
    }
    
    bool is_valid_assumption(ast_manager const & m, expr * assumption, expr * & atom) {
        if (!m.is_bool(assumption))
            return false;
        if (is_uninterp_const(assumption)) {
            atom = assumption;
            return true;
        }
        if (m.is_not(assumption, atom) && is_uninterp_const(atom))
            return true;
        return false;
    }
        
    // Throw an exception if one of the assumptions is not a literal
    void validate_assumptions(preprocessor const & p, unsigned num_assumptions, expr * const * assumptions) {
        for (unsigned i = 0; i < num_assumptions; i++) {
            expr * atom = 0;
            if (!is_valid_assumption(p.m(), assumptions[i], atom))
                throw exception("Assumptions must be Boolean variables or the negation of Boolean variables");
            if (p.is_eliminated(to_app(atom)))
                throw exception("Assumption was eliminated, we must 'freeze' variables that are used as assumptions");
        }
    }
    
    lbool solver::check_sat(unsigned num_assumptions, expr * const * assumptions) {
        commit();
        if (m_preprocessor->inconsistent())
            return l_false;
        validate_assumptions(*m_preprocessor, num_assumptions, assumptions);
#if 1
        // Temporary hack for testing 
        if (num_assumptions == 0 && m_preprocessor->size() == 0)
            return l_true;
#endif
        // TODO
        return l_undef;
    }
    
    void solver::collect_statistics(statistics & st) const {
        // TODO
    }
    
    // Return the index of the false assertion in an inconsistent m_preprocessor
    unsigned get_false_idx(preprocessor const & p) {
        SASSERT(p.inconsistent());
        // I do not assume false is stored in the end of the assertion_stack.
        unsigned i = p.size();
        while (i > 0) {
            i--;
            if (p.m().is_false(p.form(i)))
                return i;
        }
        UNREACHABLE();
        return UINT_MAX;
    }

    void solver::get_unsat_core(ptr_vector<expr> & r) {
        if (m_preprocessor->inconsistent()) {
            expr_dependency * dep = m_preprocessor->dep(get_false_idx(*m_preprocessor));
            m().linearize(dep, r);
            return;
        }
        // TODO
    }

    void solver::get_model(model_ref & md) {
#if 1
        // Temporary hack for testing
        md = alloc(model, m());
        m_preprocessor->convert(md);
#endif
        // TODO
    }

    proof * solver::get_proof() {
        if (m_preprocessor->inconsistent()) {
            return m_preprocessor->pr(get_false_idx(*m_preprocessor));
        }
        // TODO
        return 0;
    }
    
    std::string solver::reason_unknown() const {
        return "unknown";
    }
    
    void solver::get_labels(svector<symbol> & r) {
        throw exception("MCSat does not support get_labels");
    }

    void solver::freeze(func_decl * f) {
        m_preprocessor->freeze(f);
    }

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
            r->m_preprocessor->add_tactic_before(f(m, p));
        }
        sz = m_imp->m_after_tactics.size();
        for (unsigned i = 0; i < sz; i++) {
            tactic_factory & f = *(m_imp->m_after_tactics[i]);
            r->m_preprocessor->add_tactic_after(f(m, p));
        }

        sz = m_imp->m_plugins.size();
        for (unsigned i = 0; i < sz; i++) {
            r->m_kernel->add_plugin(m_imp->m_plugins.get(i));
        }
        return r;
    }

};

