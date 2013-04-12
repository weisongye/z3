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
#include"rewriter_def.h"
#include"ast_pp.h"

class qsolver_adapter : public solver {
    ast_manager &              m_manager;
    ref<solver>                m_kernel;
    // 
    quantifier_ref_vector      m_quantifiers;         // quantifiers
    expr_ref_vector            m_fresh_props;         // m_fresh_props and m_nested_quantifiers have the same size.
    quantifier_ref_vector      m_nested_quantifiers;
    obj_map<quantifier, expr*> m_nq2p;                // nested quantifiers -> fresh propositions (domain is m_nested_quantifiers)
    expr_ref_vector            m_ground_formulas; 

    bool                       m_produce_proofs;

    struct scope {
        unsigned     m_quantifiers_lim;
        unsigned     m_nested_quantifiers_lim;
        unsigned     m_ground_formulas_lim;
    };
    svector<scope>   m_scopes;

    struct cfg : public default_rewriter_cfg {
        qsolver_adapter & m;
        cfg(qsolver_adapter & _m):m(_m) {}

        bool reduce_quantifier(quantifier * old_q, 
                               expr * new_body, 
                               expr * const * new_patterns, 
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {
            // TODO proof generation
            result_pr = 0;
            quantifier * new_q = m.m().update_quantifier(old_q, new_body);
            expr * c;
            if (m.m_nq2p.find(new_q, c)) {
                result = c;
            }
            else {
                c = m.m().mk_fresh_const(0, m.m().mk_bool_sort());
                m.m_fresh_props.push_back(c);
                m.m_nested_quantifiers.push_back(new_q);
                m.m_nq2p.insert(new_q, c);
                result = c;
            }
            return true;
        }
    };

    typedef rewriter_tpl<cfg> rw;

public:
    qsolver_adapter(ast_manager & m, solver * s, params_ref const & p, bool produce_proofs, bool produce_models, bool produce_unsat_cores):
        m_manager(m),
        m_kernel(s),
        m_quantifiers(m),
        m_fresh_props(m),
        m_nested_quantifiers(m),
        m_ground_formulas(m),
        m_produce_proofs(produce_proofs) {
        m_kernel->set_produce_models(true);
    }

    virtual ~qsolver_adapter() {
    }

    ast_manager & m() const { 
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

    void display_core(std::ostream & out) const {
        out << "=== Quantifiers ===========\n";
        for (unsigned i = 0; i < m_quantifiers.size(); i++) {
            out << mk_pp(m_quantifiers.get(i), m()) << "\n";
        }        
        out << "=== Nested quantifiers ===\n";
        for (unsigned i = 0; i < m_nested_quantifiers.size(); i++) {
            out << mk_pp(m_fresh_props.get(i), m()) << " => " << mk_pp(m_nested_quantifiers.get(i), m()) << "\n";
        }
        out << "=== Ground abstraction ===\n";
        for (unsigned i = 0; i < m_ground_formulas.size(); i++) {
            out << mk_pp(m_ground_formulas.get(i), m()) << "\n";
        }        
    }
    
    virtual void set_cancel(bool f) {
        m_kernel->set_cancel(f);
    }

    virtual void push() {
        m_scopes.push_back(scope());
        scope & s                  = m_scopes.back();
        s.m_quantifiers_lim        = m_quantifiers.size();
        s.m_nested_quantifiers_lim = m_nested_quantifiers.size();
        s.m_ground_formulas_lim    = m_ground_formulas.size();
        m_kernel->push();
    }

    virtual void pop(unsigned num_scopes) {
        m_kernel->pop(num_scopes);
        SASSERT(num_scopes <= m_scopes.size());
        unsigned new_lvl    = m_scopes.size() - num_scopes;
        scope & s           = m_scopes[new_lvl];
        m_quantifiers.shrink(s.m_quantifiers_lim);
        unsigned old_nested_sz = s.m_nested_quantifiers_lim;
        SASSERT(m_nested_quantifiers.size() == m_fresh_props.size());
        SASSERT(old_nested_sz <= m_nested_quantifiers.size());
        unsigned nested_sz = m_nested_quantifiers.size();
        for (unsigned i = old_nested_sz; i < nested_sz; i++) {
            m_nq2p.erase(m_nested_quantifiers.get(i));
        }
        m_nested_quantifiers.shrink(old_nested_sz);
        m_fresh_props.shrink(old_nested_sz);
        m_ground_formulas.shrink(s.m_ground_formulas_lim);
        m_scopes.shrink(new_lvl);
    }

    virtual void abstract(expr * t, expr_ref & r, proof_ref & pr) {
        if (is_ground(t)) {
            r = t;
            pr = 0;
        }
        else if (is_quantifier(t)) {
            SASSERT(to_quantifier(t)->is_forall());
            m_quantifiers.push_back(to_quantifier(t));
            r = 0;
            pr = 0;
        }
        else {
            cfg c(*this);
            rw  proc(m(), m_produce_proofs, c);
            proc(t, r, pr);
        }
    }

    virtual void assert_expr(expr * t) {
        expr_ref  a(m());
        proof_ref pr(m());
        abstract(t, a, pr);
        if (a) {
            m_ground_formulas.push_back(a);
            m_kernel->assert_expr_proof(a, pr);
        }
    }

    virtual void assert_expr_assumption(expr * t, expr * a) {
        throw solver_exception("solver does not support assert_expr_assumption");
    }
    
    virtual void assert_expr_proof(expr * t, proof * pr) {
        expr_ref  a(m());
        proof_ref pr2(m());
        abstract(t, a, pr2);
        if (a) {
            m_ground_formulas.push_back(a);
            m_kernel->assert_expr_proof(a, m().mk_modus_ponens(pr, pr2));
        }
    }

    void get_relevant_nested_quantifiers(expr_substitution const & pM, ptr_buffer<quantifier> & result) {
        SASSERT(m_fresh_props.size() == m_nested_quantifiers.size());
        unsigned sz = m_fresh_props.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * p = m_fresh_props.get(i);
            if (pM.contains(p)) {
                result.push_back(m_nested_quantifiers.get(i));
            }
        }
    }

    lbool check_quantifiers() {
        model_ref aM;
        m_kernel->get_model(aM);
        if (!aM)
            return l_undef; // there is no model to check.
        expr_substitution pM(m());
        model2assignment proc(*(aM.get()), pM);
        proc(m_ground_formulas.size(), m_ground_formulas.c_ptr());
        ptr_buffer<quantifier> relevant_nested_quantifiers;
        get_relevant_nested_quantifiers(pM, relevant_nested_quantifiers);
        TRACE("qsolver_pm", 
              tout << "==== Partial Model\n";
              expr_substitution::iterator it  = pM.begin();
              expr_substitution::iterator end = pM.end();
              for (; it != end; ++it) {
                  tout << mk_pp(it->m_key, m()) << "\n---> " << mk_pp(it->m_value, m()) << "\n";
              }
              tout << "==== Relevant nested quantifiers\n";
              for (unsigned i = 0; i < relevant_nested_quantifiers.size(); i++) {
                  tout << mk_pp(relevant_nested_quantifiers[i], m()) << "\n";
              });
        
        // TODO: model check
        return l_true;
    }

    virtual lbool check_sat(unsigned num_assumptions, expr * const * assumptions) {
        // TEST
        TRACE("qsolver_check", tout << "before check_sat, abstraction:\n"; display_core(tout););
        while (true) {
            lbool r = m_kernel->check_sat(num_assumptions, assumptions);
            if (r == l_false)
                return r;
            r = check_quantifiers();
            if (r == l_true || r == l_undef)
                return r;
            // TODO: return unknown if maximum number of iteration exceeded
        }
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
