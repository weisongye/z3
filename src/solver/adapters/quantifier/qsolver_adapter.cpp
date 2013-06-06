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
#include"model_construct.h"
#include"model_check.h"
#include"eval_check.h"
#include"full_model_check.h"
#include"exhaustive_check.h"

#define USE_DATA_MEMBER

using namespace qsolver;

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

    //for model checking and construction
    mc_context m_mc;
    model_constructor m_mct;
    eval_check m_ec;
    full_model_check m_fmc;
    exhaustive_check m_exhc;
    bool m_fc_out;

    //statistics for quantifiers
    unsigned m_total_rounds;
    unsigned m_total_inst;
    obj_map<quantifier, unsigned> m_q_inst_round;
    obj_map<quantifier, unsigned> m_q_inst;
    unsigned m_q_next_index;

    struct scope {
        unsigned     m_quantifiers_lim;
        unsigned     m_nested_quantifiers_lim;
        unsigned     m_ground_formulas_lim;
    };
    svector<scope>   m_scopes;

    volatile bool    m_cancel;

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
        m_produce_proofs(produce_proofs),
        m_mc(m),
        m_mct(m),
        m_ec(m),
        m_fmc(m),
        m_exhc(m) {
        m_kernel->set_produce_models(true);
        m_total_rounds = 0;
        m_total_inst = 0;
        m_q_next_index = 0;
        m_cancel = false;
        m_fc_out = false;
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
        m_cancel = true;
        m_kernel->set_cancel(f);
    }

    virtual void push() {
        m_scopes.push_back(scope());
        scope & s                  = m_scopes.back();
        s.m_quantifiers_lim        = m_quantifiers.size();
        s.m_nested_quantifiers_lim = m_nested_quantifiers.size();
        s.m_ground_formulas_lim    = m_ground_formulas.size();
        m_kernel->push();
        m_mc.push();
        m_mct.push();
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
        m_mc.pop();
        m_mct.pop();
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

    void assert_expr_core(expr * t, proof * pr = 0) {
        m_ground_formulas.push_back(t);
        m_kernel->assert_expr_proof(t, pr);
    }

    virtual void assert_expr(expr * t) {
        expr_ref  a(m());
        proof_ref pr(m());
        abstract(t, a, pr);
        if (a) {
            assert_expr_core(a, pr);
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
            assert_expr_core(a, m().mk_modus_ponens(pr, pr2));
        }
    }

    void get_relevant_nested_quantifiers(expr_substitution & pM, ptr_buffer<quantifier> & result) {
        SASSERT(m_fresh_props.size() == m_nested_quantifiers.size());
        unsigned sz = m_fresh_props.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * p = m_fresh_props.get(i);
            expr * v;
            if (pM.find(p, v) && m().is_true(v)) {
                result.push_back(m_nested_quantifiers.get(i));
            }
        }
    }

    lbool check_quantifiers() {
        //std::cout << "Check quantifiers..." << std::endl;
        m_total_rounds++;
        model_ref aM;
        m_kernel->get_model(aM);
        if (!aM)
            return l_undef; // there is no model to check.
        expr_substitution pM(m());
        model2assignment proc(*(aM.get()), pM);
        proc(m_ground_formulas.size(), m_ground_formulas.c_ptr());
        ptr_buffer<quantifier> relevant_nested_quantifiers;
        get_relevant_nested_quantifiers(pM, relevant_nested_quantifiers);
        ptr_vector<quantifier> quantifiers;
        quantifiers.append(m_quantifiers.size(), m_quantifiers.c_ptr());
        quantifiers.append(relevant_nested_quantifiers.size(), relevant_nested_quantifiers.c_ptr());
        lbool result;
        expr_ref_buffer instantiation_lemmas(m_manager);
        expr_ref_buffer instantiation_lemmas_star(m_manager);
        ptr_buffer<quantifier> inst_made_this_round;
        if (m_q_next_index>=quantifiers.size()) {
            m_q_next_index = 0;
        }
        //options
        bool do_exhaustive_instantiate = false;
        bool do_eval_check = true;
        bool star_only_if_non_star = true;


        bool needs_make_model = true;
        bool round_robin = false;//true;
        bool do_continue;

        //std::cout << "Make model..." << std::endl;
        if (needs_make_model) {
            //reset the round
            m_mc.reset_round();
            m_mct.reset_round(m_mc);
            m_ec.reset_round();

            //assert the relevant quantifiers
            for (unsigned i=0; i<quantifiers.size(); i++) {
                m_mct.assert_quantifier(m_mc, quantifiers[i]);
            }
            //collect relevant terms
            for (unsigned i=0; i<m_mct.get_num_partial_model_terms(); i++) {
                proc(m_mct.get_partial_model_term(i), false);
            }
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

            //assert the partial model
            m_mct.assert_partial_model(m_mc, pM.get_map());
            //std::cout << "Produce lemmas...\n";
            //TRACE("qsolver_m",m_mct.print(tout, m_mc); }

            needs_make_model = false;
        }
        //std::cout << "Add instances..." << std::endl;
        bool continue_once = true;
        do
        {
            result = l_true;
            do_continue = false;
            m_mct.get_model_repair()->m_was_repaired = false;
            unsigned q_start = m_q_next_index;
            //check the relevant quantifiers
            for (unsigned i=0; i<quantifiers.size(); i++) {
                //get the index to process
                unsigned pr_i = round_robin ? (q_start+i)%quantifiers.size() : i;
                expr_ref_buffer instantiations(m_manager);
                expr_ref_buffer instantiations_star(m_manager);
                lbool c_result;
                if (do_exhaustive_instantiate) {
                    c_result = m_exhc.run(m_mc, &m_mct, quantifiers[pr_i], true, instantiations);
                }
                else if (do_eval_check) {
                    c_result = m_ec.run(m_mc, &m_mct, quantifiers[pr_i], instantiations);
                }
                else {
                    //check the relevant quantifiers
                    c_result = m_fmc.run(m_mc, &m_mct, quantifiers[pr_i], instantiations, instantiations_star, instantiation_lemmas.empty() || !star_only_if_non_star);
                }
                //std::cout << "current result " << (c_result==l_true ? "true" : (c_result==l_false ? "false" : "undef")) << std::endl;
                if (!instantiations.empty()) {
                    result = l_false;
                }
                else if (c_result!=l_true) {
                    result = result!=l_false ? c_result : result;
                }
                if (!instantiations.empty() || !instantiations_star.empty()) {
                    //TRACE("qsolver_q", tout << "Quantifier " << mk_pp(quantifiers[i],m_manager) << "\n";
                    //                   tout << "generated " << instantiations.size() << " " << instantiations_star.size() << std::endl;);

                    if (!inst_made_this_round.contains(quantifiers[pr_i])) {
                        inst_made_this_round.push_back(quantifiers[pr_i]);
                    }
                    if (instantiations.size()>=1000) {
                        TRACE("qsolver_q", tout << mk_pp(quantifiers[pr_i],m_manager) << " produced " << instantiations.size() << " instantiations.\n";);
                    }
                    unsigned n;
                    if (m_q_inst.find(quantifiers[pr_i], n)) {
                        m_q_inst.erase(quantifiers[pr_i]);
                        m_q_inst.insert(quantifiers[pr_i], n + instantiations.size() + instantiations_star.size());
                    }
                    else {
                        m_q_inst.insert(quantifiers[pr_i],0);
                    }

                }
                //convert and add instantiation lemmas
                if (m_nq2p.contains(quantifiers[pr_i])) {
                    expr * pv = m_nq2p.find(quantifiers[pr_i]);
                    for (unsigned j=0; j<instantiations.size(); j++) {
                        expr_ref il(m_manager);
                        il = m_manager.mk_or(m_manager.mk_not(pv), instantiations[j]);
                        instantiation_lemmas.push_back(il);
                    }
                    for (unsigned j=0; j<instantiations_star.size(); j++) {
                        expr_ref il(m_manager);
                        il = m_manager.mk_or(m_manager.mk_not(pv), instantiations_star[j]);
                        instantiation_lemmas_star.push_back(il);
                    }
                }
                else {
                    instantiation_lemmas.append(instantiations.size(), instantiations.c_ptr());
                    instantiation_lemmas_star.append(instantiations_star.size(), instantiations_star.c_ptr());
                }
                //quit if youve produced instances
                if (round_robin && !instantiation_lemmas.empty()) {
                    m_q_next_index = i+1;
                    break;
                }
            }

            if (do_eval_check) {
                if (instantiation_lemmas.empty()) {
                    do_continue = true;
                    if (!m_mct.get_model_repair()->m_was_repaired) {
                        TRACE("qsolver_q", tout << "Try full model-checking...\n";);
                        if (!m_fc_out) {
                          m_fc_out = true;
                          std::cout << "FC ";
                        }
                        do_eval_check = false;
                    }
                    else {
                        TRACE("qsolver_q", tout << "Iterate eval check, currently " << instantiation_lemmas.size() << " lemmas.\n";);
                        //std::cout << "Iterate..." << std::endl;
                    }
                }
                else {
                    //do_continue = continue_once;
                    //continue_once = false;
                 }
            }
        }
        while (do_continue);

        for (unsigned i=0; i<inst_made_this_round.size(); i++) {
            unsigned n;
            if (m_q_inst_round.find(inst_made_this_round[i], n)) {
                if (n>0 && n%5==0) {
                    TRACE("qsolver_q", tout << mk_pp(inst_made_this_round[i], m_manager) << " has produced instances on " << n << " rounds.\n";);
                }
                m_q_inst_round.erase(inst_made_this_round[i]);
                m_q_inst_round.insert(inst_made_this_round[i],n+1);
            }
            else {
                m_q_inst_round.insert(inst_made_this_round[i],0);
            }
        }

        for (unsigned i=0; i<instantiation_lemmas.size(); i++) {
            TRACE("qsolver_inst", tout << "Produced instantiation : " << mk_pp(instantiation_lemmas[i],m_manager) << "\n";);
            //std::cout << "Instantiation : " << mk_pp(instantiation_lemmas[i],m_manager) << std::endl;
            assert_expr_core(instantiation_lemmas[i]);
        }
        if (m_mct.get_model_repair()->m_stat_repairs>0) {
          TRACE("qsolver_q", tout << "...did " << m_mct.get_model_repair()->m_stat_repairs << " repairs.\n";);
          //std::cout << "...did " << m_mct.get_model_repair()->m_stat_repairs << " repairs.\n";
        }
        TRACE("qsolver_q", tout << "Produced " << instantiation_lemmas.size() << " lemmas \n";);
        //std::cout << "Produced " << instantiation_lemmas.size() << " lemmas \n";
        m_total_inst += instantiation_lemmas.size();
        if (instantiation_lemmas.empty() || !star_only_if_non_star) {
            for (unsigned i=0; i<instantiation_lemmas_star.size(); i++) {
                TRACE("qsolver_inst", tout << "Produced (star) instantiation : " << mk_pp(instantiation_lemmas_star[i],m_manager) << "\n";);
                assert_expr_core(instantiation_lemmas_star[i]);
            }
            //std::cout << "Produced " << instantiation_lemmas_star.size() << " star lemmas.\n";
            m_total_inst += instantiation_lemmas_star.size();
        }
        //std::cout << "Finished check quantifiers." << std::endl;
        return result;
    }

    virtual lbool check_sat(unsigned num_assumptions, expr * const * assumptions) {
        // TEST
        TRACE("qsolver_check", tout << "before check_sat, abstraction:\n"; display_core(tout););
        while (true) {
            if (m_cancel)
                return l_undef;
            lbool r = m_kernel->check_sat(num_assumptions, assumptions);
            if (r == l_false) {
                //std::cout << "Total inst : " << m_total_inst << "\n";
                //std::cout << "Total rounds : " << m_total_rounds << "\n";
                std::cout << m_total_inst << " " << m_total_rounds << " ";
                return r;
            }
            lbool qr = check_quantifiers();
            if (r == l_true && qr == l_true)
                return l_true;
            if (qr == l_undef)
                return l_undef; // giving up
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
