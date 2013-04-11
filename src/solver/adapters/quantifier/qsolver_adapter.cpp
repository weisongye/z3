/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    qsolver_adapter.cpp

Abstract:

    Add support for quantifiers to a ground solver.

Author:

    Leonardo de Moura (leonardo) 2013-04-09.

Revision History:

--*/
#include"qsolver_adapter.h"
#include"solver_exception.h"
#include"model2assignment.h"
#include"ast_pp.h"

class qsolver_adapter : public solver {
    ast_manager &    m_manager;
    ref<solver>      m_kernel;
    expr_ref_vector  m_abs_formulas;
    struct scope {
        unsigned     m_abs_formulas_lim;
    };
    svector<scope>   m_scopes;

public:
    qsolver_adapter(ast_manager & m, solver * s, params_ref const & p, bool produce_proofs, bool produce_models, bool produce_unsat_cores):
        m_manager(m),
        m_kernel(s),
        m_abs_formulas(m) {
        m_kernel->set_produce_models(true);
    }

    virtual ~qsolver_adapter() {
    }

    ast_manager & m() { 
        return m_manager; 
    }
    
    virtual void collect_param_descrs(param_descrs & r) {
    }
    
    virtual void set_produce_models(bool f) {
    }
    
    virtual void set_progress_callback(progress_callback * callback) {
    }
    
    virtual void updt_params(params_ref const & p) {
    }

    virtual void display(std::ostream & out) const {
        m_kernel->display(out);
    }
    
    virtual void set_cancel(bool f) {
        m_kernel->set_cancel(f);
    }

    virtual void push() {
        m_scopes.push_back(scope());
        scope & s            = m_scopes.back();
        s.m_abs_formulas_lim = m_abs_formulas.size();
        m_kernel->push();
    }

    virtual void pop(unsigned num_scopes) {
        m_kernel->pop(num_scopes);
        SASSERT(num_scopes <= m_scopes.size());
        unsigned new_lvl    = m_scopes.size() - num_scopes;
        scope & s           = m_scopes[new_lvl];
        m_abs_formulas.shrink(s.m_abs_formulas_lim);
        m_scopes.shrink(new_lvl);
    }

    virtual void abstract(expr * t, expr_ref & r) {
        // TODO
        r = t;
        m_abs_formulas.push_back(r);
    }

    virtual void assert_expr(expr * t) {
        expr_ref a(m());
        abstract(t, a);
        m_kernel->assert_expr(a);
    }

    virtual void assert_expr_assumption(expr * t, expr * a) {
        throw solver_exception("solver does not support assert_expr_assumption");
    }
    
    virtual void assert_expr_proof(expr * t, proof * pr) {
        expr_ref a(m());
        abstract(t, a);
        // TODO create new proof.
        m_kernel->assert_expr_proof(a, pr);
    }

    virtual lbool check_sat(unsigned num_assumptions, expr * const * assumptions) {
        // TEST
        lbool r = m_kernel->check_sat(num_assumptions, assumptions);
        if (r == l_false)
            return r;
        model_ref aM;
        m_kernel->get_model(aM);
        if (aM) {
            expr_substitution pM(m());
            model2assignment proc(*(aM.get()), pM);
            proc(m_abs_formulas.size(), m_abs_formulas.c_ptr());
            TRACE("qsolver", 
                  tout << "partial model\n";
                  expr_substitution::iterator it  = pM.begin();
                  expr_substitution::iterator end = pM.end();
                  for (; it != end; ++it) {
                      tout << mk_pp(it->m_key, m()) << "\n---> " << mk_pp(it->m_value, m()) << "\n";
                  });
        }
        return r;
    }

    virtual void collect_statistics(statistics & st) const {
        m_kernel->collect_statistics(st);
    }
    
    virtual void get_unsat_core(ptr_vector<expr> & r) {
        m_kernel->get_unsat_core(r);
    }
    
    virtual void get_model(model_ref & md) {
        // TODO
        m_kernel->get_model(md);
    }

    virtual proof * get_proof() {
        return 0;
    }

    virtual std::string reason_unknown() const {
        return "unknown";
    }

    virtual void get_labels(svector<symbol> & r) {
        throw solver_exception("solver does not support get_labels");
    }
};

solver * mk_qsolver_adapter(ast_manager & m, solver * s, params_ref const & p, bool produce_proofs, bool produce_models, bool produce_unsat_cores) {
    return alloc(qsolver_adapter, m, s, p, produce_proofs, produce_models, produce_unsat_cores);
}
