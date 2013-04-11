/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    pre_solver_adapter.cpp

Abstract:

    Add preprocessing capabilities to an existing solver.

Author:

    Leonardo de Moura (leonardo) 2012-11-01.

Revision History:

--*/
#include"pre_solver_adapter.h"
#include"solver_exception.h"
#include"tactic.h"
#include"params.h"
#include"scoped_ptr_vector.h"
#include"assertion_stack.h"

struct pre_solver_adapter::imp {
    ast_manager &        m_manager;
    ref<solver>          m_kernel;
    assertion_stack      m_stack;
    tactic_ref_vector    m_before_tactics;
    tactic_ref_vector    m_after_tactics;
    ptr_vector<expr>     m_extra_assumptions;
    obj_hashtable<expr>  m_extra_assumptions_set;
    expr_ref_vector      m_new_exprs;
    struct scope {
        unsigned        m_extra_assumptions_lim;
        unsigned        m_new_exprs_lim;
    };
    svector<scope>      m_scopes;
    
    imp(ast_manager & m, solver * s, params_ref const & p, bool produce_proofs, bool produce_models, bool produce_unsat_cores):
        m_manager(m),
        m_kernel(s),
        m_stack(m, produce_proofs, produce_models, produce_unsat_cores),
        m_new_exprs(m) {
    }
    
    ast_manager & m() const { return m_manager; }
    
    static void set_cancel(sref_vector<tactic> & ts, bool f) {
        for (unsigned i = 0; i < ts.size(); i++) {
            ts[i]->set_cancel(f);
        }
    }
    
    void set_cancel(bool f) {
        set_cancel(m_before_tactics, f);
        set_cancel(m_after_tactics, f);
        m_kernel->set_cancel(f);
    }
    
    bool proofs_enabled() const {
        return m_stack.proofs_enabled();
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
        throw solver_exception("Assumptions must be Boolean variables or the negation of Boolean variables");
    }
    
    /**
       \brief Convert an expression e with dependency d into 
       a clause of the form d => e
    */
    expr * exprdep2expr(expr * e, expr_dependency * d) {
        if (d == 0)
            return e;
        if (proofs_enabled()) {
            throw solver_exception("Tracked assertions cannot be used when proof generation is enabled.");
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
    
    void add_tactic_before(tactic * t) {
        SASSERT(m_stack.scope_lvl() == 0);
        m_before_tactics.push_back(t);
    }
    
    void add_tactic_after(tactic * t) {
        SASSERT(m_stack.scope_lvl() == 0);
        m_after_tactics.push_back(t);
    }
    
    void apply_tactics() {
        unsigned i = m_before_tactics.size();
        while (i > 0) {
            --i;
            (*m_before_tactics[i])(m_stack);
        }
        
        for (unsigned i = 0; i < m_after_tactics.size(); i++) {
            (*m_after_tactics[i])(m_stack);
        }
    }
    
    void commit() {
        unsigned qhead = m_stack.qhead();
        apply_tactics();
        m_stack.commit();
        if (!m_stack.inconsistent()) {
            unsigned sz    = m_stack.size();
            for (unsigned i = qhead; i < sz; i++) {
                expr * e = exprdep2expr(m_stack.form(i), m_stack.dep(i));
                m_kernel->assert_expr_proof(e, m_stack.pr(i));
            }
        }
    }
    
    void push() {
        commit();
        m_scopes.push_back(scope());
        scope & s = m_scopes.back();
        s.m_new_exprs_lim         = m_new_exprs.size();
        s.m_extra_assumptions_lim = m_extra_assumptions.size();
        m_stack.push();
        m_kernel->push();
    }
    
    void pop(unsigned num_scopes) {
        m_stack.pop(num_scopes);
        m_kernel->pop(num_scopes);
        
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
    
    void assert_expr_assumption(expr * t, expr * a) {
        proof * pr = proofs_enabled() ? m().mk_asserted(t) : 0;
        expr_dependency * dep = (a && m_stack.unsat_core_enabled()) ? m().mk_leaf(a) : 0;
        m_stack.assert_expr(t, pr, dep);
    }
    
    void assert_expr(expr * t) {
        proof * pr = proofs_enabled() ? m().mk_asserted(t) : 0;
        m_stack.assert_expr(t, pr, 0);
    }

    void assert_expr_proof(expr * t, proof * pr) {
        if (proofs_enabled())
            pr = pr == 0 ? m().mk_asserted(t) : pr;
        else
            pr = 0;
        m_stack.assert_expr(t, pr, 0);
    }
    
    // Throw an exception if one of the assumptions is not a literal
    void validate_assumptions(unsigned num_assumptions, expr * const * assumptions) {
        for (unsigned i = 0; i < num_assumptions; i++) {
            expr * atom = 0;
            if (!is_valid_assumption(assumptions[i], atom))
                throw_invalid_assumption();
            if (m_stack.is_eliminated(to_app(atom)))
                throw solver_exception("Assumption was eliminated, we must 'freeze' variables that are used as assumptions");
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

    lbool check_sat_core(unsigned num_assumptions, expr * const * assumptions) {
        TRACE("pre_solver", m_kernel->display(tout); tout << "\n";);
        lbool r = m_kernel->check_sat(num_assumptions, assumptions);
        return r;
    }
    
    lbool check_sat(unsigned num_assumptions, expr * const * assumptions) {
        commit();
        if (m_stack.inconsistent())
            return l_false;
        validate_assumptions(num_assumptions, assumptions);
        if (m_extra_assumptions.empty()) {
            return check_sat_core(num_assumptions, assumptions);
        }
        else {
            scoped_append append(m_extra_assumptions, num_assumptions, assumptions);
            return check_sat_core(m_extra_assumptions.size(), m_extra_assumptions.c_ptr());
        }
    }
    
    // Return the index of the false assertion in an inconsistent m_stack
    unsigned get_false_idx() {
        SASSERT(m_stack.inconsistent());
        // I do not assume false is stored in the end of the assertion_stack.
        unsigned i = m_stack.size();
        while (i > 0) {
            i--;
            if (m().is_false(m_stack.form(i)))
                return i;
        }
        UNREACHABLE();
        return UINT_MAX;
    }
    
    void get_unsat_core(ptr_vector<expr> & r) {
        if (m_stack.inconsistent()) {
            expr_dependency * dep = m_stack.dep(get_false_idx());
            m().linearize(dep, r);
            return;
        }
        m_kernel->get_unsat_core(r);
    }
    
    void get_model(model_ref & md) {
        m_kernel->get_model(md);
        m_stack.convert(md);
    }
    
    proof * get_proof() {
        if (m_stack.inconsistent())
            return m_stack.pr(get_false_idx());
        else
            return m_kernel->get_proof();
    }
    
    std::string reason_unknown() const {
        return m_kernel->reason_unknown();
    }
    
    void collect_statistics(statistics & st) const {
        // TODO: collect preprocessor statistics?
        m_kernel->collect_statistics(st);
    }

    static void updt_params(sref_vector<tactic> & ts, params_ref const & p) {
        for (unsigned i = 0; i < ts.size(); i++) {
            ts[i]->updt_params(p);
        }
    }

    void updt_params(params_ref const & p) {
        m_kernel->updt_params(p);
        updt_params(m_before_tactics, p);
        updt_params(m_after_tactics, p);
    }
};

pre_solver_adapter::pre_solver_adapter(ast_manager & m, solver * s, params_ref const & p, bool produce_proofs, bool produce_models, bool produce_unsat_cores) {
    m_imp = alloc(imp, m, s, p, produce_proofs, produce_models, produce_unsat_cores);
}

pre_solver_adapter::~pre_solver_adapter() {
    dealloc(m_imp);
}

void pre_solver_adapter::add_tactic_before(tactic * t) {
    m_imp->add_tactic_before(t);
}

void pre_solver_adapter::add_tactic_after(tactic * t) {
    m_imp->add_tactic_after(t);
}

void pre_solver_adapter::collect_param_descrs(param_descrs & r) {
    // do nothing
    m_imp->m_kernel->collect_param_descrs(r);
}

void pre_solver_adapter::set_produce_models(bool f) {
    m_imp->m_kernel->set_produce_models(f);
}

void pre_solver_adapter::set_progress_callback(progress_callback * callback) {
    m_imp->m_kernel->set_progress_callback(callback);
}

void pre_solver_adapter::updt_params(params_ref const & p) {
    m_imp->updt_params(p);
}

void pre_solver_adapter::set_cancel(bool f) {
    m_imp->set_cancel(f);
}

unsigned pre_solver_adapter::get_num_assertions() const {
    return m_imp->m_stack.size();
}

expr * pre_solver_adapter::get_assertion(unsigned idx) const {
    return m_imp->m_stack.form(idx);
}

void pre_solver_adapter::display(std::ostream & out) const {
    m_imp->m_stack.display(out);
}

unsigned pre_solver_adapter::get_scope_level() const {
    return m_imp->m_stack.scope_lvl();
}

void pre_solver_adapter::push() {
    m_imp->push();
}

void pre_solver_adapter::pop(unsigned n) {
    m_imp->pop(n);
}

void pre_solver_adapter::assert_expr_assumption(expr * t, expr * a) {
    m_imp->assert_expr_assumption(t, a);
}

void pre_solver_adapter::assert_expr(expr * t) {
    m_imp->assert_expr(t);
}

void pre_solver_adapter::assert_expr_proof(expr * t, proof * pr) {
    m_imp->assert_expr_proof(t, pr);
}

lbool pre_solver_adapter::check_sat(unsigned num_assumptions, expr * const * assumptions) {
    return m_imp->check_sat(num_assumptions, assumptions);
}

void pre_solver_adapter::collect_statistics(statistics & st) const {
    m_imp->collect_statistics(st);
}

void pre_solver_adapter::get_unsat_core(ptr_vector<expr> & r) {
    m_imp->get_unsat_core(r);
}

void pre_solver_adapter::get_model(model_ref & md) {
    m_imp->get_model(md);
}

proof * pre_solver_adapter::get_proof() {
    return m_imp->get_proof();
}

std::string pre_solver_adapter::reason_unknown() const {
    return m_imp->reason_unknown();
}

void pre_solver_adapter::get_labels(svector<symbol> & r) {
    throw solver_exception("Solver does not support get_labels");
}

void pre_solver_adapter::freeze(func_decl * f) {
    m_imp->m_stack.freeze(f);
}

struct pre_solver_adapter_factory::imp {
    scoped_ptr_vector<tactic_factory> m_before_tactics;
    scoped_ptr_vector<tactic_factory> m_after_tactics;
};

pre_solver_adapter_factory::pre_solver_adapter_factory() {
    m_imp = alloc(imp);
}

pre_solver_adapter_factory::~pre_solver_adapter_factory() {
    dealloc(m_imp);
}
    
void pre_solver_adapter_factory::add_tactic_before(tactic_factory * f) {
    m_imp->m_before_tactics.push_back(f);
}

void pre_solver_adapter_factory::add_tactic_after(tactic_factory * f) {
    m_imp->m_after_tactics.push_back(f);
}

solver * pre_solver_adapter_factory::operator()(ast_manager & m, params_ref const & p, bool proofs_enabled, bool models_enabled, bool unsat_core_enabled, symbol const & logic) {
    pre_solver_adapter * r = mk_solver(m, p, proofs_enabled, models_enabled, unsat_core_enabled, logic);
    unsigned sz = m_imp->m_before_tactics.size();
    for (unsigned i = 0; i < sz; i++) {
        tactic_factory & f = *(m_imp->m_before_tactics[i]);
        r->m_imp->add_tactic_before(f(m, p));
    }
    sz = m_imp->m_after_tactics.size();
    for (unsigned i = 0; i < sz; i++) {
        tactic_factory & f = *(m_imp->m_after_tactics[i]);
        r->m_imp->add_tactic_after(f(m, p));
    }
    return r;
}

