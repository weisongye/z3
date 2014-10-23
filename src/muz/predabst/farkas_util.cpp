/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

	farkas_util.cpp

Abstract:

	Utilities for applying farkas lemma over linear implications.

Author:

	Tewodros A. Beyene (t-tewbe) 2014-10-22.

Revision History:

--*/

#include "farkas_util.h"

vector<expr_ref_vector> pair_set_to_set2(vector<expr_ref_vector> fmls1, vector<expr_ref_vector> fmls2, ast_manager& m){
	vector<expr_ref_vector> result;
	for (unsigned i = 0; i < fmls1.size(); ++i) {
		for (unsigned j = 0; j < fmls2.size(); ++j) {
			expr_ref_vector entry(m);
			entry.append(fmls1[i]);
			entry.append(fmls2[j]);
			result.push_back(entry);
		}
	}
	return result;
}

vector<expr_ref_vector> cnf_to_dnf2(vector<vector<expr_ref_vector> > cnf_sets, ast_manager& m){

	SASSERT(cnf_sets.size() >= 2);
	vector<expr_ref_vector> result;

	result = pair_set_to_set2(cnf_sets[0], cnf_sets[1], m);
	if (cnf_sets.size() == 2){
		return result;
	}
	else{
		for (unsigned i = 2; i < cnf_sets.size(); ++i) {
			result = pair_set_to_set2(result, cnf_sets[i], m);
		}
		return result;
	}
}

expr_ref neg_expr(expr_ref& fml){
	ast_manager& m = fml.get_manager();
	reg_decl_plugins(m);
	arith_util a(m);
	expr *e1, *e2;

	expr_ref new_formula(m);

	if (m.is_eq(fml, e1, e2)){
		new_formula = m.mk_or(a.mk_lt(e1, e2), a.mk_gt(e1, e2));
	}
	else if (a.is_lt(fml, e1, e2)){
		new_formula = a.mk_ge(e1, e2);
	}
	else if (a.is_le(fml, e1, e2)){
		new_formula = a.mk_gt(e1, e2);
	}
	else if (a.is_gt(fml, e1, e2)){
		new_formula = a.mk_le(e1, e2);
	}
	else if (a.is_ge(fml, e1, e2)){
		new_formula = a.mk_lt(e1, e2);
	}
	else {
		new_formula = fml;
	}
	return new_formula;
}

struct norm_formula{
	expr_ref m_norm_fml;
	vector<expr_ref_vector> m_norm_struct;

	vector<expr_ref_vector> to_dnf_struct(expr_ref fml){

		ast_manager& m = fml.get_manager();
		reg_decl_plugins(m);
		arith_util a(m);
		vector<expr_ref_vector> dnf_formula;

		if (m.is_and(fml)){

			expr_ref_vector sub_formulas(m);
			vector<vector<expr_ref_vector> > dnf_sub_formulas;
			sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());

			for (unsigned i = 0; i < sub_formulas.size(); ++i) {
				dnf_sub_formulas.push_back(to_dnf_struct(expr_ref(sub_formulas[i].get(), m)));
			}
			dnf_formula = cnf_to_dnf2(dnf_sub_formulas, m);
		}
		else if (m.is_or(fml)){
			expr_ref_vector sub_formulas(m);
			vector<vector<expr_ref_vector> > dnf_sub_formulas;
			sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());

			for (unsigned i = 0; i < sub_formulas.size(); ++i) {
				dnf_formula.append(to_dnf_struct(expr_ref(sub_formulas[i].get(), m)));
			}
		}
		else {
			expr_ref_vector tmp(m);
			tmp.push_back(fml.get());
			dnf_formula.push_back(tmp);

		}
		return dnf_formula;
	}

	expr_ref to_dnf_formula(vector<expr_ref_vector> dnf_struct, ast_manager& m)
	{
		expr_ref_vector disjs(m);
		for (unsigned i = 0; i < dnf_struct.size(); ++i) {
			disjs.push_back(expr_ref(m.mk_and(dnf_struct[i].size(), dnf_struct[i].c_ptr()), m));
		}
		return expr_ref(m.mk_or(disjs.size(), disjs.c_ptr()), m);
	}

	expr_ref neg_formula(expr_ref fml){
		ast_manager& m = fml.get_manager();
		reg_decl_plugins(m);
		arith_util a(m);

		expr_ref new_formula(m);
		if (m.is_and(fml)){

			expr_ref_vector sub_formulas(m);
			expr_ref_vector new_sub_formulas(m);

			sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
			for (unsigned i = 0; i < sub_formulas.size(); ++i) {
				expr_ref tmp_fml1(m), tmp_fml2(m);
				tmp_fml1 = sub_formulas[i].get();
				tmp_fml2 = neg_formula(tmp_fml1);
				new_sub_formulas.push_back(tmp_fml2.get());
			}

			new_formula = m.mk_or(new_sub_formulas.size(), new_sub_formulas.c_ptr());

		}
		else if (m.is_or(fml)){

			expr_ref_vector sub_formulas(m);
			expr_ref_vector new_sub_formulas(m);

			sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
			for (unsigned i = 0; i < sub_formulas.size(); ++i) {
				expr_ref tmp_fml1(m), tmp_fml2(m);
				tmp_fml1 = sub_formulas[i].get();
				tmp_fml2 = neg_formula(tmp_fml1);
				new_sub_formulas.push_back(tmp_fml2.get());
			}

			new_formula = m.mk_and(sub_formulas.size(), new_sub_formulas.c_ptr());
		}
		else if (m.is_not(fml)){

			expr_ref_vector sub_formulas(m);
			expr_ref_vector new_sub_formulas(m);

			sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());

			new_formula = sub_formulas[0].get();
		}
		else {
			new_formula = neg_expr(fml);
		}
		return new_formula;
	}

	//public:
	norm_formula(expr_ref input_fml) : m_norm_fml(input_fml){
	}

	void normalize(){ //negate and to DNF (struct as well as formula)
		m_norm_struct = to_dnf_struct(neg_formula(m_norm_fml));
		m_norm_fml = to_dnf_formula(m_norm_struct, m_norm_fml.get_manager());
	}

	expr_ref get_formula(){
		return m_norm_fml;
	}

	vector<expr_ref_vector>  get_struct(){
		return m_norm_struct;
	}

};

bool exists_valid(expr_ref& formula, expr_ref_vector vars, expr_ref& constraint_st) {
	ast_manager& m = formula.get_manager();
	reg_decl_plugins(m);
	arith_util arith(m);
	norm_formula n_form(formula);
	//std::cout << "Input formula F: \n" << mk_pp(n_form.get_formula(), m) << "\n";
	n_form.normalize();
	//std::cout << "Normalized formula dnf(not(F)): \n" << mk_pp(n_form.get_formula(), m) << "\n";
	//SASSERT(m.is_or(n_form));
	expr_ref_vector disjs(m);
	disjs.append(to_app(n_form.get_formula())->get_num_args(), to_app(n_form.get_formula())->get_args());
	expr_ref fml_false(m.mk_false(), m);
	for (unsigned i = 0; i < disjs.size(); ++i) {
		farkas_imp f_imp(vars);
		f_imp.set(expr_ref(disjs[i].get(), m), fml_false);
		if (f_imp.solve_constraint()) {
			constraint_st = m.mk_and(constraint_st, f_imp.get_constraints());
		}
		else {
			return false;
		}
	}
	return true;
}

bool well_founded(expr_ref_vector vsws, expr_ref& LHS, expr_ref& sol_bound, expr_ref& sol_decrease){
	ast_manager& m = LHS.get_manager();
	arith_util arith(m);

	SASSERT(!m.is_true(LHS));
	SASSERT(m.is_and(LHS));
	SASSERT(to_app(LHS)->get_num_args > 1);
	
	SASSERT((vsws.size() % 2) == 0);
	expr_ref_vector vs(m), ws(m);
	for (unsigned i = 0; i < vsws.size(); i++){
		if (i < (vsws.size() / 2)){
			vs.push_back(vsws[i].get());
		}
		else {
			ws.push_back(vsws[i].get());
		}
	}

	expr_ref_vector params(m);
	expr_ref sum_psvs(arith.mk_numeral(rational(0), true), m);
	expr_ref sum_psws(arith.mk_numeral(rational(0), true), m);

	for (unsigned i = 0; i < vs.size(); ++i) {
		expr_ref param(m.mk_fresh_const("p", arith.mk_int()), m);
		params.push_back(param);
		sum_psvs = arith.mk_add(sum_psvs.get(), arith.mk_mul(param.get(), vs[i].get()));
		sum_psws = arith.mk_add(sum_psws.get(), arith.mk_mul(param.get(), ws[i].get()));
	}

	expr_ref delta0(m.mk_const(symbol("delta0"), arith.mk_int()), m);
	params.push_back(delta0);

	expr_ref bound(arith.mk_ge(sum_psvs, delta0), m);
	expr_ref decrease(arith.mk_lt(sum_psws, sum_psvs), m);
	expr_ref to_solve(m.mk_or(m.mk_not(LHS), m.mk_and(bound, decrease)), m);

	expr_ref constraint_st(m.mk_true(), m);
	if (exists_valid(to_solve, vsws, constraint_st)) {
		smt_params new_param;
		smt::kernel solver(m, new_param);
		solver.assert_expr(constraint_st);
		if (solver.check() == l_true){
			expr_ref_vector values(m);
			model_ref modref;
			solver.get_model(modref);
			expr_ref value(m);

			for (unsigned j = 0; j < params.size(); j++) {
				if (modref.get()->eval(params[j].get(), value, true)) {
					values.push_back(value);
				}
				else {
					return false;
				}
			}
			expr_ref sol_delta0(values[vs.size()-1].get(), m);
			//values.pop_back();
			expr_ref sol_sum_psvs(arith.mk_numeral(rational(0), true), m);
			expr_ref sol_sum_psws(arith.mk_numeral(rational(0), true), m);

			for (unsigned i = 0; i < values.size()-1; ++i) {
				sol_sum_psvs = arith.mk_add(sol_sum_psvs.get(), arith.mk_mul(values[i].get(), vs[i].get()));
				sol_sum_psws = arith.mk_add(sol_sum_psws.get(), arith.mk_mul(values[i].get(), ws[i].get()));
			}
			sol_bound = arith.mk_ge(sol_sum_psvs, sol_delta0);
			sol_decrease = arith.mk_lt(sol_sum_psws, sol_sum_psvs);
			return true;
		}
		else {
			return false;
		}
	}
	else {
		return false;
	}

}

void mk_bilin_lambda_constraint(vector<lambda_kind> lambda_kinds, int max_lambda, expr_ref& cons){
	ast_manager& m = cons.get_manager();
	//reg_decl_plugins(m);
	arith_util arith(m);

	expr_ref n1(arith.mk_numeral(rational(1), true), m);
	expr_ref nminus1(arith.mk_numeral(rational(-1), true), m);

	int min_lambda = -1 * max_lambda;

	for (unsigned i = 0; i < lambda_kinds.size(); i++) {

		if (lambda_kinds[i].m_kind == bilin_sing){
			cons = m.mk_and(cons, m.mk_or(m.mk_eq(lambda_kinds[i].m_lambda, nminus1), m.mk_eq(lambda_kinds[i].m_lambda.get(), n1)));
		}
		else if (lambda_kinds[i].m_kind == bilin){
			if (lambda_kinds[i].m_op != 0)  min_lambda = 0; // operator not equality
			expr_ref bilin_disj(m.mk_true(), m);
			for (int j = min_lambda; j <= max_lambda; j++)
				bilin_disj = m.mk_or(bilin_disj, m.mk_eq(lambda_kinds[i].m_lambda.get(), arith.mk_numeral(rational(j), true)));
			cons = m.mk_and(cons, bilin_disj);
		}
	}
}

void mk_bound_pairs(vector<lambda_kind>& lambda_kinds, int lin_max_lambda, int bilin_max_lambda){

	for (unsigned i = 0; i < lambda_kinds.size(); i++) {
		if (lambda_kinds[i].m_kind == bilin_sing){
			lambda_kinds[i].m_lower_bound = -1;
			lambda_kinds[i].m_upper_bound = 1;
		}
		else {
			int min_lambda;
			if (lambda_kinds[i].m_kind == bilin){
				min_lambda = -1 * bilin_max_lambda;
				lambda_kinds[i].m_upper_bound = bilin_max_lambda;
			}
			else {
				min_lambda = -1 * lin_max_lambda;
				lambda_kinds[i].m_upper_bound = lin_max_lambda;
			}

			if (lambda_kinds[i].m_op == 0){
				lambda_kinds[i].m_lower_bound = min_lambda;
			}
			else {
				lambda_kinds[i].m_lower_bound = 0;
			}

		}
	}
}

expr_ref_vector get_all_vars(expr_ref& fml){
	ast_manager& m = fml.get_manager();
	expr_ref_vector m_todo(m);
	expr_ref_vector vars(m);
	m_todo.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
	while (!m_todo.empty()) {
		expr* e = m_todo.back();
		m_todo.pop_back();
		switch (e->get_kind()) {
		case AST_VAR: {
			if(!vars.contains(e)) vars.push_back(e);
			break;
		}
		case AST_APP: {
			m_todo.append(to_app(e)->get_num_args(), to_app(e)->get_args());
			break;
		}
		default:
			UNREACHABLE();
			break;
		}
	}
	return vars;
}

