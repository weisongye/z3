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

    struct solver::imp {
        ast_manager &       m_manager;
        preprocessor        m_preprocessor;
        kernel              m_kernel;
        ptr_vector<expr>    m_extra_assumptions;
        obj_hashtable<expr> m_extra_assumptions_set;
        expr_ref_vector     m_new_exprs;
        struct scope {
            unsigned        m_extra_assumptions_lim;
            unsigned        m_new_exprs_lim;
        };
        svector<scope>      m_scopes;

        imp(ast_manager & m, params_ref const & p, bool produce_proofs, bool produce_models, bool produce_unsat_cores):
            m_manager(m),
            m_preprocessor(m, produce_proofs, produce_models, produce_unsat_cores),
            m_kernel(m, produce_proofs),
            m_new_exprs(m) {
        }

        ast_manager & m() const { return m_manager; }

        void set_cancel(bool f) {
            m_preprocessor.set_cancel(f);
            m_kernel.set_cancel(f);
        }

        bool proofs_enabled() const {
            return m_preprocessor.proofs_enabled();
        }
        
        // Return true if assumption is a valid/acceptable assumption/answer literal.
        bool is_valid_assumption(expr * assumption, expr * & atom) const {
            if (!m().is_bool(assumption))
                return false;
            if (is_uninterp_const(assumption)) {
                atom = assumption;
                return true;
            }
            if (m().is_not(assumption, atom) && is_uninterp_const(atom))
                return true;
            return false;
        }

        bool is_valid_assumption(expr * assumption) const {
            expr * atom;
            return is_valid_assumption(assumption, atom);
        }

        void throw_invalid_assumption() {
            throw exception("Assumptions must be Boolean variables or the negation of Boolean variables");
        }

        /**
           \brief Convert an expression e with dependency d into 
           a clause of the form d => e
        */
        expr * exprdep2expr(expr * e, expr_dependency * d) {
            if (d == 0)
                return e;
            if (proofs_enabled()) {
                throw exception("Tracked assertions cannot be used when proof generation is enabled.");
            }
            ptr_vector<expr> answer_lits;
            m().linearize(d, answer_lits);
            if (answer_lits.empty())
                return e;
            expr_ref_vector new_clause_lits(m());
            // register answer_lits in m_extra_assumptions, and
            // create new clause
            for (unsigned i = 0; i < answer_lits.size(); i++) {
                expr * l = answer_lits[i];
                if (!is_valid_assumption(l))
                    throw_invalid_assumption();
                if (!m_extra_assumptions_set.contains(l)) {
                    m_extra_assumptions_set.insert(l);
                    m_extra_assumptions.push_back(l);
                }
                expr * atom;
                if (m().is_not(l, atom))
                    new_clause_lits.push_back(atom);
                else 
                    new_clause_lits.push_back(m().mk_not(atom));
            }
            new_clause_lits.push_back(e);
            SASSERT(new_clause_lits.size() >= 2);
            expr * r = m().mk_or(new_clause_lits.size(), new_clause_lits.c_ptr());
            m_new_exprs.push_back(r);
            return r;
        }
        
        void commit() {
            unsigned qhead = m_preprocessor.qhead();
            m_preprocessor.commit();
            if (!m_preprocessor.inconsistent()) {
                unsigned sz    = m_preprocessor.size();
                for (unsigned i = qhead; i < sz; i++) {
                    expr * e = exprdep2expr(m_preprocessor.form(i), m_preprocessor.dep(i));
                    m_kernel.assert_expr(e, m_preprocessor.pr(i));
                }
            }
        }
        
        void push() {
            commit();
            m_scopes.push_back(scope());
            scope & s = m_scopes.back();
            s.m_new_exprs_lim         = m_new_exprs.size();
            s.m_extra_assumptions_lim = m_extra_assumptions.size();
            m_preprocessor.push();
            m_kernel.push();
        }
    
        void pop(unsigned num_scopes) {
            m_preprocessor.pop(num_scopes);
            m_kernel.pop(num_scopes);

            SASSERT(num_scopes <= m_scopes.size());
            unsigned new_lvl    = m_scopes.size() - num_scopes;
            scope & s           = m_scopes[new_lvl];
            for (unsigned i = s.m_extra_assumptions_lim; i < m_extra_assumptions.size(); i++) {
                m_extra_assumptions_set.erase(m_extra_assumptions[i]);        
            }
            m_extra_assumptions.shrink(s.m_extra_assumptions_lim);
            m_new_exprs.shrink(s.m_new_exprs_lim);
            m_scopes.shrink(new_lvl);
        }

        void assert_expr(expr * t, expr * a) {
            proof * pr = proofs_enabled() ? m().mk_asserted(t) : 0;
            expr_dependency * dep = (a && m_preprocessor.unsat_core_enabled()) ? m().mk_leaf(a) : 0;
            m_preprocessor.assert_expr(t, pr, dep);
        }

        void assert_expr(expr * t) {
            proof * pr = proofs_enabled() ? m().mk_asserted(t) : 0;
            m_preprocessor.assert_expr(t, pr, 0);
        }
       
        // Throw an exception if one of the assumptions is not a literal
        void validate_assumptions(unsigned num_assumptions, expr * const * assumptions) {
            for (unsigned i = 0; i < num_assumptions; i++) {
                expr * atom = 0;
                if (!is_valid_assumption(assumptions[i], atom))
                    throw_invalid_assumption();
                if (m_preprocessor.is_eliminated(to_app(atom)))
                    throw exception("Assumption was eliminated, we must 'freeze' variables that are used as assumptions");
            }
        }

        struct scoped_append {
            ptr_vector<expr> & m_extra_assumptions;
            unsigned           m_old_size;
            scoped_append(ptr_vector<expr> & v, unsigned num_assumptions, expr * const * assumptions):
                m_extra_assumptions(v),
                m_old_size(v.size()) {
                m_extra_assumptions.append(num_assumptions, assumptions);
            }
            ~scoped_append() {
                m_extra_assumptions.shrink(m_old_size);
            }
        };

        lbool check_sat(unsigned num_assumptions, expr * const * assumptions) {
            commit();
            if (m_preprocessor.inconsistent())
                return l_false;
            validate_assumptions(num_assumptions, assumptions);
            if (m_extra_assumptions.empty()) {
                return m_kernel.check_sat(num_assumptions, assumptions);
            }
            else {
                scoped_append append(m_extra_assumptions, num_assumptions, assumptions);
                return m_kernel.check_sat(m_extra_assumptions.size(), m_extra_assumptions.c_ptr());
            }
        }
        
        // Return the index of the false assertion in an inconsistent m_preprocessor
        unsigned get_false_idx() {
            SASSERT(m_preprocessor.inconsistent());
            // I do not assume false is stored in the end of the assertion_stack.
            unsigned i = m_preprocessor.size();
            while (i > 0) {
                i--;
                if (m().is_false(m_preprocessor.form(i)))
                    return i;
            }
            UNREACHABLE();
            return UINT_MAX;
        }
        
        void get_unsat_core(ptr_vector<expr> & r) {
            if (m_preprocessor.inconsistent()) {
                expr_dependency * dep = m_preprocessor.dep(get_false_idx());
                m().linearize(dep, r);
                return;
            }
            m_kernel.get_unsat_core(r);
        }
        
        void get_model(model_ref & md) {
            m_kernel.get_model(md);
            m_preprocessor.convert(md);
        }

        proof * get_proof() {
            if (m_preprocessor.inconsistent())
                return m_preprocessor.pr(get_false_idx());
            else
                return m_kernel.get_proof();
        }
    
        std::string reason_unknown() const {
            return m_kernel.reason_unknown();
        }

        void collect_statistics(statistics & st) const {
            // TODO: collect preprocessor statistics?
            m_kernel.collect_statistics(st);
        }
        
    };

    solver::solver(ast_manager & m, params_ref const & p, bool produce_proofs, bool produce_models, bool produce_unsat_cores) {
        m_imp = alloc(imp, m, p, produce_proofs, produce_models, produce_unsat_cores);
    }
    
    solver::~solver() {
        dealloc(m_imp);
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
        // TODO
    }
    
    void solver::set_cancel(bool f) {
        m_imp->set_cancel(f);
    }
        
    unsigned solver::get_num_assertions() const {
        return m_imp->m_preprocessor.size();
    }
    
    expr * solver::get_assertion(unsigned idx) const {
        return m_imp->m_preprocessor.form(idx);
    }
        
    void solver::display(std::ostream & out) const {
        m_imp->m_preprocessor.display(out);
    }
    
    unsigned solver::get_scope_level() const {
        return m_imp->m_preprocessor.scope_lvl();
    }

    
    void solver::push() {
        m_imp->push();
    }
    
    void solver::pop(unsigned n) {
        m_imp->pop(n);
    }
    
    void solver::assert_expr(expr * t, expr * a) {
        m_imp->assert_expr(t, a);
    }
    
    void solver::assert_expr(expr * t) {
        m_imp->assert_expr(t);
    }
    
    lbool solver::check_sat(unsigned num_assumptions, expr * const * assumptions) {
        return m_imp->check_sat(num_assumptions, assumptions);
    }
    
    void solver::collect_statistics(statistics & st) const {
        m_imp->collect_statistics(st);
    }
    
    void solver::get_unsat_core(ptr_vector<expr> & r) {
        m_imp->get_unsat_core(r);
    }

    void solver::get_model(model_ref & md) {
        m_imp->get_model(md);
    }

    proof * solver::get_proof() {
        return m_imp->get_proof();
    }
    
    std::string solver::reason_unknown() const {
        return m_imp->reason_unknown();
    }
    
    void solver::get_labels(svector<symbol> & r) {
        throw exception("MCSat does not support get_labels");
    }

    void solver::freeze(func_decl * f) {
        m_imp->m_preprocessor.freeze(f);
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
            r->m_imp->m_preprocessor.add_tactic_before(f(m, p));
        }
        sz = m_imp->m_after_tactics.size();
        for (unsigned i = 0; i < sz; i++) {
            tactic_factory & f = *(m_imp->m_after_tactics[i]);
            r->m_imp->m_preprocessor.add_tactic_after(f(m, p));
        }

        sz = m_imp->m_plugins.size();
        for (unsigned i = 0; i < sz; i++) {
            r->m_imp->m_kernel.add_plugin(m_imp->m_plugins.get(i));
        }
        return r;
    }

};

