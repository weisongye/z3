/*++
Copyright (c) 2013 Microsoft Corporation

Module Name: 

	farkas_util.h

Abstract:

	Utilities for applying farkas lemma over linear implications.

Author:

	Tewodros A. Beyene (t-tewbe) 2014-10-22.

Revision History:

--*/
#include "th_rewriter.h"
#include "smt2parser.h"
#include "arith_decl_plugin.h"
#include "reg_decl_plugins.h"
#include "arith_rewriter.h"
#include "ast_pp.h"
#include "smt_kernel.h"
#include "smt_params.h"
#include "model.h"
#include "model2expr.h"
#include "model_smt2_pp.h"
#include "ast_counter.h"
#include "dl_util.h"



typedef enum  { bilin_sing, bilin, lin } lambda_kind_sort;

struct lambda_kind {
	expr_ref m_lambda;
	lambda_kind_sort m_kind;
	unsigned m_op;
	int m_lower_bound;
	int m_upper_bound;

	lambda_kind(expr_ref in_lambda, lambda_kind_sort in_kind, unsigned in_op) :
		m_lambda(in_lambda), m_kind(in_kind), m_op(in_op),
		m_lower_bound(0),
		m_upper_bound(0){
	}
};

static expr_ref_vector get_all_terms(expr_ref term){
	ast_manager& m = term.get_manager();
	arith_util arith(m);
	expr_ref_vector all_facts(m);
	//if (to_app(term)->get_num_args() == 0){
	if (!arith.is_mul(term.get())){
		all_facts.push_back(term);
	}
	else {
		SASSERT(arith.is_mul(term.get()));
		expr_ref_vector facts(m);
		facts.append(to_app(term)->get_num_args(), to_app(term)->get_args());
		for (unsigned i = 0; i < facts.size(); ++i) {
			all_facts.append(get_all_terms(expr_ref(facts[i].get(), m)));
		}
	}
	return all_facts;
}

class farkas_pred{
	expr_ref_vector m_vars;
	expr_ref_vector m_coeffs;
	unsigned m_op;
	expr_ref m_const;

	bool m_has_params;

	expr_ref rewrite_pred(expr_ref& term) {
		ast_manager& m = term.get_manager();
		arith_util arith(m);
		th_rewriter rw(m);

		expr *e1, *e2;
		expr_ref n_minus1(arith.mk_numeral(rational(-1), true), m);

		if (m.is_eq(term, e1, e2)){
			term = arith.mk_sub(e1, e2);
			m_op = 0;
		}
		else if (arith.is_le(term, e1, e2)){
			term = arith.mk_sub(e1, e2);
		}
		else if (arith.is_ge(term, e1, e2)){
			term = arith.mk_sub(e2, e1);
		}
		else if (arith.is_lt(term, e1, e2)){
			term = arith.mk_sub(expr_ref(arith.mk_sub(e1, e2), m), n_minus1);
		}
		else if (arith.is_gt(term, e1, e2)){
			term = arith.mk_sub(expr_ref(arith.mk_sub(e2, e1), m), n_minus1);
		}
		else {
			std::cout << " Don't know" << std::endl;
			SASSERT(false);
		}
		rw(term);
		return term;
	}

	void extend_coeffs(expr_ref_vector p_vars, expr_ref_vector p_coeffs){
		ast_manager& m = m_vars.get_manager();
		arith_util arith(m);

		expr_ref n0(arith.mk_numeral(rational(0), true), m);
		for (unsigned i = 0; i < m_vars.size(); ++i) {
			m_coeffs.push_back(n0);
		}
		for (unsigned i = 0; i < m_vars.size(); ++i) {
			for (unsigned j = 0; j < p_vars.size(); ++j) {
				if (m_vars[i].get() == p_vars[j].get()){
					m_coeffs.set(i, p_coeffs[j].get());
					p_vars.erase(j);
					p_coeffs.erase(j);
					break;
				}
			}
		}
	}

	void set(expr_ref& term) {
		ast_manager& m = term.get_manager();
		arith_util arith(m);

		term = rewrite_pred(term);
		SASSERT(arith.is_add(term.get()));

		//std::cout << "Re-written input :  " << mk_pp(term.get(), m) << "\n";

		expr_ref_vector p_coeffs(m);
		expr_ref_vector p_vars(m);
		expr_ref_vector p_const_facts(m);

		expr_ref n0(arith.mk_numeral(rational(0), true), m);
		expr_ref n1(arith.mk_numeral(rational(1), true), m);

		expr_ref_vector add_facts(m);
		add_facts.append(to_app(term)->get_num_args(), to_app(term)->get_args());

		for (unsigned i = 0; i < add_facts.size(); ++i) {

			expr_ref_vector mul_facts(m);
			expr_ref mul_term(add_facts[i].get(), m);
			mul_facts.append(get_all_terms(mul_term));

			SASSERT(mul_facts.size() <= 3);

			expr_ref_vector var_mul_facts(m);
			expr_ref_vector const_mul_facts(m);

			//std::cout << "Mul fact size: " << mul_facts.size() << "\n";
			for (unsigned j = 0; j < mul_facts.size(); ++j) {
				//std::cout << "Mul fact  " << j << ": " << mk_pp(mul_facts[j].get(), m) << "  ";
				expr_ref tmp(mul_facts[j].get(), m);
				if (m_vars.contains(tmp)) {
					var_mul_facts.push_back(tmp);
				}
				else {
					const_mul_facts.push_back(tmp);
					if (m_has_params == false && !arith.is_numeral(tmp)){
						m_has_params = true;
					}
				}
			}
			//std::cout << "\n";
			SASSERT(var_mul_facts.size() <= 1);
			if (var_mul_facts.size() == 0){
				p_const_facts.push_back(mul_term);
			}
			else {
				if (const_mul_facts.size() == 0){
					p_vars.push_back(mul_term);
					p_coeffs.push_back(n1);
				}
				else if (const_mul_facts.size() == 1){
					expr_ref tmp1(var_mul_facts[0].get(), m);
					p_vars.push_back(tmp1);
					expr_ref tmp2(const_mul_facts[0].get(), m);
					p_coeffs.push_back(tmp2);
				}
				else {
					expr_ref tmp1(var_mul_facts[0].get(), m);
					p_vars.push_back(tmp1);
					expr_ref tmp2(arith.mk_mul(const_mul_facts.size(), const_mul_facts.c_ptr()), m);
					p_coeffs.push_back(tmp2);
				}
			}
		}

		th_rewriter rw(m);
		if (p_const_facts.size() == 0){
			m_const = n0;
		}
		else if (p_const_facts.size() == 1){
			//m_const = expr_ref(p_const_facts[0].get(), m);
			m_const = expr_ref(arith.mk_uminus(p_const_facts[0].get()), m);
			rw(m_const);
		}
		else {
			//m_const = arith.mk_add(p_const_facts.size(), p_const_facts.c_ptr());
			m_const = expr_ref(arith.mk_uminus(arith.mk_add(p_const_facts.size(), p_const_facts.c_ptr())), m);
			rw(m_const);
		}
		extend_coeffs(p_vars, p_coeffs);
	}

public:

	farkas_pred(expr_ref_vector vars) : m_vars(vars), m_coeffs(vars.get_manager()),
		m_const(vars.get_manager()), m_op(1), m_has_params(false){
	}

	farkas_pred(expr_ref_vector vars, expr_ref_vector in_coeffs, unsigned in_op, expr_ref in_const) :
		m_vars(vars), m_coeffs(in_coeffs),
		m_const(in_const), m_op(in_op), m_has_params(false){
	}

	void put(expr_ref term){

		ast_manager& m = term.get_manager();
		arith_util arith(m);

		expr_ref n0(arith.mk_numeral(rational(0), true), m);
		expr_ref n_minus1(arith.mk_numeral(rational(-1), true), m);

		//std::cout << "Orig input :  " << mk_pp(term.get(), m) << "\n";
		if (m.is_true(term)){

			for (unsigned i = 0; i < m_vars.size(); ++i) {
				m_coeffs.push_back(n0);
			}
			m_op = 1;
			m_const = n0;

		}
		else if (m.is_false(term)) {

			for (unsigned i = 0; i < m_vars.size(); ++i) {
				m_coeffs.push_back(n0);
			}
			m_op = 1;
			m_const = n_minus1;
		}
		else {
			set(term);
		}

	}

	expr_ref_vector get_coeffs(){
		return m_coeffs;
	}

	unsigned get_op(){
		return m_op;
	}

	expr_ref get_const(){
		return m_const;
	}

	bool has_params() {
		return m_has_params;
	}

	void display(){
		ast_manager& m = m_vars.get_manager();
		for (unsigned i = 0; i < m_vars.size(); ++i) {
			if (i == 0){
				std::cout << mk_pp(m_coeffs[i].get(), m) << " * " << mk_pp(m_vars[i].get(), m);
			}
			else{
				std::cout << " + " << mk_pp(m_coeffs[i].get(), m) << " * " << mk_pp(m_vars[i].get(), m);
			}
		}

		switch (m_op) {
		case 0: std::cout << " = "; break;
		case 1: std::cout << " =< "; break;
		case 2: std::cout << " >= "; break;
		case 3: std::cout << " < "; break;
		case 4: std::cout << " > "; break;
		default:
			std::cout << " Unknown relation! ";
			break;
		}

		std::cout << mk_pp(m_const.get(), m) << "\n";

		if (m_has_params){
			std::cout << "Params? : TRUE \n";
		}
		else{
			std::cout << "Params? : FALSE \n";
		}

	}


};

class farkas_conj{
	expr_ref_vector m_vars;
	vector<expr_ref_vector> m_set_coeffs;
	vector<unsigned> m_set_op;
	vector<expr_ref> m_set_const;

	unsigned m_param_pred_count;

	void add_more(farkas_pred& f_pred){
		ast_manager& m = m_vars.get_manager();
		expr_ref_vector new_coeffs(m);
		new_coeffs.append(f_pred.get_coeffs());
		//std::cout << "ADD: To farkas preds \n";
		if (f_pred.has_params()){
			m_param_pred_count++;
			for (unsigned i = 0; i < m_vars.size(); ++i) {
				m_set_coeffs[i].reverse();
				m_set_coeffs[i].push_back(expr_ref(new_coeffs[i].get(), m));
				m_set_coeffs[i].reverse();
			}
			m_set_op.reverse();
			m_set_op.push_back(f_pred.get_op());
			m_set_op.reverse();
			m_set_const.reverse();
			m_set_const.push_back(f_pred.get_const());
			m_set_const.reverse();

		}
		else {
			for (unsigned i = 0; i < m_vars.size(); ++i) {
				m_set_coeffs[i].push_back(expr_ref(new_coeffs[i].get(), m));
			}
			m_set_op.push_back(f_pred.get_op());
			m_set_const.push_back(f_pred.get_const());
		}
	}

	void init(farkas_pred& f_pred){
		ast_manager& m = m_vars.get_manager();
		expr_ref_vector new_coeffs(m);
		new_coeffs.append(f_pred.get_coeffs());
		//std::cout << "INIT: To farkas preds, vars " << m_vars.size() << "\n";
		for (unsigned i = 0; i < m_vars.size(); ++i) {
			expr_ref_vector init_coeff(m);
			init_coeff.push_back(expr_ref(new_coeffs[i].get(), m));
			m_set_coeffs.push_back(init_coeff);
		}
		m_set_op.push_back(f_pred.get_op());
		m_set_const.push_back(f_pred.get_const());
		if (f_pred.has_params()) {
			m_param_pred_count++;
		}
	}

public:
	farkas_conj(expr_ref_vector vars) : m_vars(vars), m_param_pred_count(0){
	}

	void add(farkas_pred& f_pred){
		if (m_set_coeffs.size() == 0) {
			init(f_pred);
		}
		else{
			add_more(f_pred);
		}
	}

	vector<expr_ref_vector> get_set_coeffs(){
		return m_set_coeffs;
	}

	vector<expr_ref> get_set_const(){
		return m_set_const;
	}

	vector<unsigned> get_ops(){
		return  m_set_op;
	}

	unsigned conj_size(){
		return m_set_op.size();
	}

	unsigned get_param_pred_count(){
		return m_param_pred_count;
	}

	void display(){
		ast_manager& m = m_vars.get_manager();
		for (unsigned i = 0; i < m_vars.size(); ++i) {
			std::cout << mk_pp(m_vars[i].get(), m) << "   ";
		}
		std::cout << "\n";
		for (unsigned i = 0; i < m_set_coeffs[0].size(); ++i) {
			for (unsigned j = 0; j < m_vars.size(); ++j) {
				std::cout << mk_pp(m_set_coeffs[j][i].get(), m) << "   ";
			}
			std::cout << m_set_op[i] << "   " << mk_pp(m_set_const[i].get(), m) << "\n";
		}
	}

};

class farkas_imp{
	expr_ref_vector m_vars;
	farkas_conj m_lhs;
	farkas_pred m_rhs;
	expr_ref_vector m_lambdas;
	expr_ref_vector m_solutions;
	expr_ref m_constraints;

	vector<lambda_kind> m_lambda_kinds;


	void set_constraint(){
		ast_manager& m = m_vars.get_manager();
		reg_decl_plugins(m);
		arith_util arith(m);

		SASSERT(m_lhs.get_param_pred_count() > 0);

		unsigned no_vars = m_vars.size();
		unsigned no_preds = m_lhs.conj_size();
		//std::cout << "Preds No: " << no_preds << " and Vars No: " << no_vars << "\n";

		for (unsigned i = 0; i < no_preds; i++) {
			expr_ref lambda(m.mk_fresh_const("t", arith.mk_int()), m);
			m_lambdas.push_back(lambda);
			//m_lambdas.push_back(expr_ref(m.mk_const(symbol(i), arith.mk_int()), m));
		}

		expr_ref n0(arith.mk_numeral(rational(0), true), m);
		expr_ref n1(arith.mk_numeral(rational(1), true), m);


		for (unsigned i = 0; i < no_preds; ++i) {
			if (m_lhs.get_ops()[i] == 1){
				m_constraints = m.mk_and(m_constraints.get(), arith.mk_ge(m_lambdas[i].get(), n0.get()));
			}
		}

		set_lambda_kinds();

		for (unsigned i = 0; i < no_vars; ++i) {
			expr_ref ith_m_rhs((m_rhs.get_coeffs()[i]).get(), m);
			expr_ref sum(arith.mk_numeral(rational(0), true), m);
			for (unsigned j = 0; j < no_preds; ++j) {
				expr_ref jth_m_lhs((m_lhs.get_set_coeffs()[i][j]).get(), m);
				sum = arith.mk_add(sum.get(), arith.mk_mul(m_lambdas[j].get(), jth_m_lhs.get()));
			}
			m_constraints = m.mk_and(m_constraints.get(), m.mk_eq(sum.get(), ith_m_rhs.get()));
		}

		expr_ref rhs_const((m_rhs.get_const()).get(), m);
		expr_ref sum_const(arith.mk_numeral(rational(0), true), m);
		for (unsigned j = 0; j < no_preds; ++j) {
			expr_ref jth_m_lhs_const((m_lhs.get_set_const()[j]).get(), m);
			sum_const = arith.mk_add(sum_const.get(), arith.mk_mul(m_lambdas[j].get(), jth_m_lhs_const.get()));
		}
		m_constraints = m.mk_and(m_constraints.get(), arith.mk_le(sum_const.get(), rhs_const.get()));
		//std::cout << mk_pp(m_constraints, m) << "\n";
	}

	void set_lambda_kinds(){
		ast_manager& m = m_vars.get_manager();
		reg_decl_plugins(m);
		arith_util arith(m);

		unsigned lhs_params_count = m_lhs.get_param_pred_count();
		if (lhs_params_count == 1) {
			if (m_lhs.get_ops()[0] == 0){
				m_lambda_kinds.push_back(lambda_kind(expr_ref(m_lambdas[0].get(), m), bilin_sing, m_lhs.get_ops()[0]));
			}
			else {
				expr_ref n1(arith.mk_numeral(rational(1), true), m);
				m_constraints = m.mk_and(m_constraints.get(), m.mk_eq(m_lambdas[0].get(), n1.get()));
			}
		}
		else {
			for (unsigned i = 0; i < m_lhs.conj_size(); ++i) {
				if (i < lhs_params_count){
					m_lambda_kinds.push_back(lambda_kind(expr_ref(m_lambdas[i].get(), m), bilin, m_lhs.get_ops()[i]));
				}
				else {
					m_lambda_kinds.push_back(lambda_kind(expr_ref(m_lambdas[i].get(), m), lin, m_lhs.get_ops()[i]));
				}
			}
		}
	}


public:
	farkas_imp(expr_ref_vector vars) : m_vars(vars), m_lhs(vars), m_rhs(vars),
		m_lambdas(vars.get_manager()), m_solutions(vars.get_manager()),
		m_constraints((vars.get_manager()).mk_true(), vars.get_manager()){
	}

	void set(expr_ref lhs_term, expr_ref& rhs_term) {
		ast_manager& m = m_vars.get_manager();
		expr_ref_vector conjs(m);
		conjs.append(to_app(lhs_term)->get_num_args(), to_app(lhs_term)->get_args());
		for (unsigned i = 0; i < conjs.size(); ++i) {
			//std::cout << "Conj " << i << " : ";
			//std::cout << "Input to pred " << mk_pp(conjs[i].get(), m) << "\n";
			farkas_pred f_pred(m_vars);
			f_pred.put(expr_ref(conjs[i].get(), m));
			//f_pred.display();
			m_lhs.add(f_pred);
		}
		m_rhs.put(rhs_term);
		set_constraint();
	}

	bool solve_constraint(){
		ast_manager& m = m_vars.get_manager();
		smt_params new_param;;
		smt::kernel solver(m, new_param);

		solver.assert_expr(m_constraints);
		bool has_sol = true;

		if (solver.check() == l_true){
			model_ref modref;
			solver.get_model(modref);
			expr_ref solution(m);
			for (unsigned j = 0; j < m_lhs.conj_size(); ++j) {
				if (modref.get()->eval(m_lambdas[j].get(), solution, true)) {
					m_solutions.push_back(solution);
				}
				else {
					return 0;
				}
			}
			return 1;
		}
		else {
			return 0;
		}
	}

	expr_ref_vector get_lambdas(){
		return m_lambdas;
	}

	expr_ref_vector get_solutions(){
		return m_solutions;
	}

	expr_ref get_constraints(){
		return m_constraints;
	}

	void display(){
		ast_manager m = m_vars.get_manager();
		std::cout << "LHS: \n";
		m_lhs.display();
		std::cout << "RHS: \n";
		m_rhs.display();
		std::cout << "Constraint: \n" << mk_pp(m_constraints.get(), m) << "\n";
		if (m_solutions.size() > 0) {
			std::cout << "Solutions: \n";
		}
		for (unsigned i = 0; i < m_solutions.size(); ++i) {
			std::cout << mk_pp(m_lambdas[i].get(), m) << " --> " << mk_pp(m_solutions[i].get(), m) << "\n";
		}
	}

};

bool exists_valid(expr_ref& formula, expr_ref_vector vars, expr_ref& constraint_st);

bool well_founded(expr_ref_vector vars, expr_ref& LHS, expr_ref& bound, expr_ref& decrease);

expr_ref_vector get_all_vars(expr_ref& fml);
