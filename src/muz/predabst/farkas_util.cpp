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


vector<expr_ref_vector> cnf_to_dnf_struct(vector<vector<expr_ref_vector> > cnf_sets){
	SASSERT(cnf_sets.size() >= 2);
	vector<expr_ref_vector> result(cnf_sets.get(0));
	for (unsigned k = 1; k < cnf_sets.size(); ++k){
		vector<expr_ref_vector> sub_result;
		for (unsigned i = 0; i < result.size(); ++i)
			for (unsigned j = 0; j < cnf_sets.get(k).size(); ++j) {
			expr_ref_vector entry(result[i]);
			entry.append(cnf_sets.get(k)[j]);
			sub_result.push_back(entry);
			}
		result = sub_result;
	}

	return result;
}

expr_ref neg_expr(expr_ref& fml){
	ast_manager& m = fml.get_manager();
	std::cout << "in2negexpr: " << mk_pp(fml, m) << "\n";
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
	std::cout << "out2negexpr: " << mk_pp(new_formula, m) << "\n";
	return new_formula;
}

vector<expr_ref_vector> to_dnf_struct(expr_ref fml){
		vector<expr_ref_vector> dnf_struct;
		expr_ref_vector sub_formulas(fml.m());
		if (fml.m().is_and(fml)){
			vector<vector<expr_ref_vector> > dnf_sub_structs;
			sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
			for (unsigned i = 0; i < sub_formulas.size(); ++i)
				dnf_sub_structs.push_back(to_dnf_struct(expr_ref(sub_formulas[i].get(), fml.m())));
			return cnf_to_dnf_struct(dnf_sub_structs);
		}
		else if (fml.m().is_or(fml)){
			sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
			for (unsigned i = 0; i < sub_formulas.size(); ++i)
				dnf_struct.append(to_dnf_struct(expr_ref(sub_formulas[i].get(), fml.m())));
		}
		else {
			expr_ref_vector tmp(fml.m());
			tmp.push_back(fml);
			dnf_struct.push_back(tmp);
		}
		return dnf_struct;
	}

expr_ref non_neg_formula(expr_ref fml);

expr_ref neg_formula(expr_ref fml){
		ast_manager& m = fml.get_manager();
		std::cout << "in2neg: " << mk_pp(fml, m) << "\n";
		expr_ref_vector sub_formulas(m);
		expr_ref_vector new_sub_formulas(m);
		if (m.is_and(fml)){
			sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
			for (unsigned i = 0; i < sub_formulas.size(); ++i) {
				new_sub_formulas.push_back(neg_formula(expr_ref(sub_formulas[i].get(), m)));
			}
			expr_ref ee1(m.mk_or(new_sub_formulas.size(), new_sub_formulas.c_ptr()), m);
			std::cout << "out2neg: " << mk_pp(ee1, m) << "\n";
			return ee1;
//			return expr_ref(m.mk_or(new_sub_formulas.size(), new_sub_formulas.c_ptr()), m);
		}
		else if (m.is_or(fml)){
			sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
			for (unsigned i = 0; i < sub_formulas.size(); ++i) {
				new_sub_formulas.push_back(neg_formula(expr_ref(sub_formulas[i].get(), m)));
			}
			expr_ref ee2(m.mk_and(sub_formulas.size(), new_sub_formulas.c_ptr()), m);
			std::cout << "out2neg: " << mk_pp(ee2, m) << "\n";
			return ee2;

			//return expr_ref(m.mk_and(sub_formulas.size(), new_sub_formulas.c_ptr()), m);
		}
		else if (m.is_not(fml)){
			expr_ref ee3(to_app(fml)->get_arg(0), m);
			expr_ref ee5(non_neg_formula(ee3));

			std::cout << "out2neg: " << mk_pp(ee5, m) << "\n";
			return ee5;

			//return expr_ref(to_app(fml)->get_arg(0), m);
		}
		else {
			expr_ref ee4(neg_expr(fml), m);
			std::cout << "out2neg: " << mk_pp(ee4, m) << "\n";
			return ee4;


//			return neg_expr(fml);
		}
	}

expr_ref non_neg_formula(expr_ref fml){
	ast_manager& m = fml.get_manager();
	expr_ref_vector sub_formulas(m);
	expr_ref_vector new_sub_formulas(m);
	if (m.is_and(fml)){
		sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
		for (unsigned i = 0; i < sub_formulas.size(); ++i) {
			new_sub_formulas.push_back(non_neg_formula(expr_ref(sub_formulas[i].get(), m)));
		}
		expr_ref ee1(m.mk_and(new_sub_formulas.size(), new_sub_formulas.c_ptr()), m);
		return ee1;
	}
	else if (m.is_or(fml)){
		sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
		for (unsigned i = 0; i < sub_formulas.size(); ++i) {
			new_sub_formulas.push_back(non_neg_formula(expr_ref(sub_formulas[i].get(), m)));
		}
		expr_ref ee2(m.mk_or(sub_formulas.size(), new_sub_formulas.c_ptr()), m);
		return ee2;
	}
	else if (m.is_not(fml)){
		expr_ref ee3(to_app(fml)->get_arg(0), m);
		expr_ref ee5(neg_formula(ee3));
		return ee5;
	}
	else {
		return fml;
	}
}

expr_ref neg_and_2dnf(expr_ref fml){
		vector<expr_ref_vector> dnf_struct;
		dnf_struct = to_dnf_struct(neg_formula(fml));
		expr_ref_vector disjs(fml.m());
		for (unsigned i = 0; i < dnf_struct.size(); ++i) {
			disjs.push_back(fml.m().mk_and(dnf_struct[i].size(), dnf_struct[i].c_ptr()));
		}
		return expr_ref(fml.m().mk_or(disjs.size(), disjs.c_ptr()), fml.m());
	}

void mk_binder(expr_ref_vector vars, expr_ref_vector args, expr_ref& cs){
	SASSERT(vars.size() == args.size());
	for (unsigned i = 0; i < vars.size(); i++){
		if (vars.m().is_true(cs))
			cs = vars.m().mk_eq(vars.get(i), args.get(i));
		else
			cs = vars.m().mk_and(cs, vars.m().mk_eq(vars.get(i), args.get(i)));
	}
}

bool exists_valid(expr_ref& fml, expr_ref_vector vars, expr_ref& constraint_st) {
	expr_ref norm_fml(fml.m());
	norm_fml = neg_and_2dnf(fml);
	SASSERT(fml.m().is_or(norm_fml));
	expr_ref_vector disjs(fml.m());
	disjs.append(to_app(norm_fml)->get_num_args(), to_app(norm_fml)->get_args());
	for (unsigned i = 0; i < disjs.size(); ++i) {
		farkas_imp f_imp(vars);
		f_imp.set(expr_ref(disjs.get(i), fml.m()), expr_ref(fml.m().mk_false(), fml.m()));
		if (f_imp.solve_constraint())
			constraint_st = fml.m().mk_and(constraint_st, f_imp.get_constraints());
		else
			return false;
	}
	return true;
}

bool mk_exists_forall_farkas(expr_ref& fml, expr_ref_vector vars, expr_ref& constraint_st, bool mk_lambda_kinds, vector<lambda_kind>& all_lambda_kinds) {
	std::cout << "in mk_exists_forall_farkas 0...\n";
	std::cout << "fml: " << mk_pp(fml.get(), fml.m()) << "\n";
	expr_ref norm_fml(neg_and_2dnf(fml));
	std::cout << "norm_fml: " << mk_pp(norm_fml, norm_fml.m()) << "\n";

	SASSERT(fml.m().is_or(norm_fml));
	expr_ref_vector disjs(fml.m());
	disjs.append(to_app(norm_fml)->get_num_args(), to_app(norm_fml)->get_args());
	std::cout << "in mk_exists_forall_farkas 1...\n";
	for (unsigned i = 0; i < disjs.size(); ++i) {
		std::cout << "in mk_exists_forall_farkas 2...\n";
		farkas_imp f_imp(vars, mk_lambda_kinds);
		std::cout << "in mk_exists_forall_farkas 3...\n";
		f_imp.set(expr_ref(disjs[i].get(), fml.m()), expr_ref(fml.m().mk_false(), fml.m()));
		f_imp.display();
		std::cout << "in mk_exists_forall_farkas 4...\n";
		if (f_imp.solve_constraint()) {
			std::cout << "in mk_exists_forall_farkas 5...\n";
			//std::cout << "constraint_st: " << mk_pp(constraint_st, norm_fml.m()) << "\n";
			//std::cout << "f_imp.get_constraints(): " << mk_pp(f_imp.get_constraints(), norm_fml.m()) << "\n";

			constraint_st = fml.m().mk_and(constraint_st, f_imp.get_constraints());
			std::cout << "in mk_exists_forall_farkas 6...\n";
			all_lambda_kinds.append(f_imp.get_lambda_kinds());
			std::cout << "in mk_exists_forall_farkas 7...\n";

		}
		else
			return false;
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

	std::cout << "bound: " << mk_pp(bound, m) << "\n";
	std::cout << "decrease: " << mk_pp(decrease, m) << "\n";

	expr_ref constraint_st(m.mk_true(), m);
	if (exists_valid(to_solve, vsws, constraint_st)) {
		smt_params new_param;
		smt::kernel solver(m, new_param);
		solver.assert_expr(constraint_st);
		if (solver.check() == l_true){
			expr_ref_vector values(m);
			model_ref modref;
			solver.get_model(modref);
			if (modref.get()->eval(bound.get(), sol_bound) && modref.get()->eval(decrease.get(), sol_decrease)) {
				return true;
			}			
			return false; // when does it happen?		
		}
		return false; //unsat param
	}
	return false; //unsat lambda
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


static expr_ref_vector get_all_pred_vars(expr_ref& fml){
	ast_manager& m = fml.get_manager();
	expr_ref_vector m_todo(m);
	expr_ref_vector vars(m);
	m_todo.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
	while (!m_todo.empty()) {
		expr* e = m_todo.back();
		m_todo.pop_back();
		switch (e->get_kind()) {
		case AST_VAR: {
			if (!vars.contains(e)) vars.push_back(e);
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

 expr_ref_vector get_all_vars(expr_ref& fml){
	ast_manager& m = fml.get_manager();
	if (m.is_and(fml) || m.is_or(fml)){
		expr_ref_vector all_vars(m);
		expr_ref_vector sub_formulas(m);
		sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
		for (unsigned i = 0; i < sub_formulas.size(); ++i)
			all_vars.append(get_all_vars(expr_ref(sub_formulas[i].get(), m)));
		return all_vars;
	}
	else if (m.is_not(fml)){
		return get_all_vars(expr_ref(to_app(fml)->get_arg(0), m));
	}
	else {
		if (is_func_decl(fml)){
			return expr_ref_vector(m, to_app(fml)->get_num_args(), to_app(fml)->get_args());
		}
		else {
			return get_all_pred_vars(fml);
		}
	}
}

expr_ref_vector vars_difference(expr_ref_vector source, expr_ref_vector to_remove){
	expr_ref_vector diff(source.get_manager());
	for (unsigned i = 0; i < source.size(); i++)
		if (!to_remove.contains(source[i].get())) diff.push_back(source[i].get());
	return diff;
}

expr_ref rel_template::subst_template_body(expr_ref fml, func_decl2body map){
	ast_manager& m = fml.get_manager();
	expr_ref new_formula(m);
	expr_ref_vector sub_formulas(m);
	expr_ref_vector new_sub_formulas(m);

	if (m.is_and(fml)){
		sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
		for (unsigned i = 0; i < sub_formulas.size(); ++i)
			new_sub_formulas.push_back(subst_template_body(expr_ref(sub_formulas[i].get(), m), map).get());
		new_formula = m.mk_and(new_sub_formulas.size(), new_sub_formulas.c_ptr());
	}
	else if (m.is_or(fml)){
		sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
		for (unsigned i = 0; i < sub_formulas.size(); ++i)
			new_sub_formulas.push_back(subst_template_body(expr_ref(sub_formulas[i].get(), m), map).get());
		new_formula = m.mk_or(new_sub_formulas.size(), new_sub_formulas.c_ptr());

	}
	else if (m.is_not(fml)){
		sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
		new_formula = m.mk_not(subst_template_body(expr_ref(sub_formulas[0].get(), m), map));
	}
	else {

		if (is_func_decl(fml)){
			func_decl2body::obj_map_entry* e = map.find_core(to_app(fml));
			if (!e) return fml;
			return expr_ref(e->get_data().get_value(), m);
		}
	}
	return new_formula;
}

expr_ref rel_template_suit::subst_template_body(expr_ref fml, vector<rel_template2> rel_templates, expr_ref_vector& args_coll){
	ast_manager& m = fml.get_manager();
	expr_ref new_formula(m);
	expr_ref_vector sub_formulas(m);
	expr_ref_vector new_sub_formulas(m);
	//std::cout << "****** in subst : " << mk_pp(fml, m_rel_manager) << "\n";

	if (m.is_and(fml)){

		//std::cout << "and subst : " << mk_pp(fml, m_rel_manager) << "\n";
		sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
		for (unsigned i = 0; i < sub_formulas.size(); ++i){
			new_sub_formulas.push_back(subst_template_body(expr_ref(sub_formulas[i].get(), m), rel_templates, args_coll).get());
		}
		new_formula = m.mk_and(new_sub_formulas.size(), new_sub_formulas.c_ptr());
	}
	else if (m.is_or(fml)){
		//std::cout << "or subst : " << mk_pp(fml, m_rel_manager) << "\n";
		sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
		for (unsigned i = 0; i < sub_formulas.size(); ++i){
			new_sub_formulas.push_back(subst_template_body(expr_ref(sub_formulas[i].get(), m), rel_templates, args_coll).get());
		}
		new_formula = m.mk_or(new_sub_formulas.size(), new_sub_formulas.c_ptr());

	}
	else if (m.is_not(fml)){
		//std::cout << "not subst : " << mk_pp(fml, m_rel_manager) << "\n";
		sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
		new_formula = m.mk_not(subst_template_body(expr_ref(sub_formulas[0].get(), m), rel_templates, args_coll));
	}
	else {
		//app* mm = to_app(fml);
		//std::cout << "No of args: " << mm->get_num_args() << "\n";
		if (m_names.contains(to_app(fml)->get_decl()->get_name())){
			//std::cout << "func decl subst : " << mk_pp(fml, m_rel_manager) << "\n";
			for (unsigned i = 0; i < rel_templates.size(); i++){
				if (to_app(fml)->get_decl()->get_name() == rel_templates.get(i).m_head->get_decl()->get_name()) {
					expr_ref cs(m.mk_true(), m);
					expr_ref_vector args(m, to_app(fml)->get_decl()->get_arity(), to_app(fml)->get_args());
					args_coll.append(args);
					mk_binder(args, m_temp_subst, cs);
					return  expr_ref(m.mk_and(cs, m_rel_templates.get(i).m_body), m);
				}
			}
		}
		//std::cout << "misc subst : " << mk_pp(fml, m_rel_manager) << "\n";
		return fml;
	}
	return new_formula;
}
