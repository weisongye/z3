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

bool mk_exists_forall_farkas(expr_ref& fml, expr_ref_vector vars, expr_ref& constraint_st, bool mk_lambda_kinds, vector<lambda_kind>& all_lambda_kinds) {
	ast_manager& m = fml.get_manager();
	
	norm_formula n_form(fml);
	n_form.normalize();
	SASSERT(m.is_or(n_form.get_formula()));

	expr_ref_vector disjs(m);
	disjs.append(to_app(n_form.get_formula())->get_num_args(), to_app(n_form.get_formula())->get_args());
	expr_ref fml_false(m.mk_false(), m);
	for (unsigned i = 0; i < disjs.size(); ++i) {
		farkas_imp f_imp(vars, mk_lambda_kinds);
		f_imp.set(expr_ref(disjs[i].get(), m), fml_false);
		if (f_imp.solve_constraint()) {
			constraint_st = m.mk_and(constraint_st, f_imp.get_constraints());
			all_lambda_kinds.append(f_imp.get_lambda_kinds());
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

static expr_ref_vector get_all_vars(expr_ref& fml){
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

static expr_ref_vector vars_difference(expr_ref_vector source, expr_ref_vector to_remove){
	expr_ref_vector diff(source.get_manager());
	for (unsigned i = 0; i < source.size(); i++)
		if (!to_remove.contains(source[i].get())) diff.push_back(source[i].get());
	return diff;
}

class rel_template {

	typedef obj_map<app, expr*> func_decl2body;
	typedef obj_map<app, std::pair<expr* const*, expr*> > func_decl2params_body;
	typedef obj_map<app, expr*> func_decl2inst;

	func_decl2params_body m_map;
	expr_ref m_extras;
	expr_ref m_acc;

	func_decl2inst m_rel_template_instances;

	vector<symbol> m_names;
	expr_ref_vector m_params;

	expr_ref subst_template_body(expr_ref fml, func_decl2params_body map);

public:

	void process_template(app* head, expr_ref body, expr_ref extra){
		func_decl2body in_rel_templates;
		in_rel_templates.insert(head, body);
		process_template(in_rel_templates, extra);
	}
	
	void process_template(func_decl2body in_rel_templates, expr_ref extra){
		ast_manager m;
		func_decl2body::iterator it = in_rel_templates.begin();
		func_decl2body::iterator end = in_rel_templates.end();

		for (; it != end; ++it){
			symbol head_name = it->m_key->get_decl()->get_name();
			if (m_names.contains(head_name)){
				std::cout << "Multiple templates found for : " << head_name.str() << "\n";
				throw(head_name);
			}
			else {
				expr_ref_vector body_vars(get_all_vars(expr_ref(it->get_value(), m)));
				expr_ref_vector head_vars(m, it->m_key->get_num_args(), it->m_key->get_args());
				expr_ref_vector temp_params(m);
				for (unsigned j = 0; j < body_vars.size(); j++)
					if (!head_vars.contains(body_vars[j].get())) temp_params.push_back(body_vars[j].get());
				m_map.insert(it->m_key, std::make_pair(temp_params.c_ptr(), it->m_value));
				m_names.push_back(head_name);
				m_params.append(temp_params);
			}
		}
		m_extras = m.mk_and(m_extras, extra);
	}

	void constrain_template(expr_ref fml){
		ast_manager& m = fml.get_manager();
		m_acc = m.mk_and(fml, m_acc); //updating the constraint store
		instantiate_template(fml);
	}

	void instantiate_template(expr_ref fml){
		ast_manager& m = m_acc.get_manager();
		expr_ref m_acc_subst(subst_template_body(m_acc, m_map));
		expr_ref farkas_cons(m), lambda_cons(m);
		vector<lambda_kind> all_lambda_kinds;
		expr_ref_vector all_vars(get_all_vars(fml));
		expr_ref_vector vars(vars_difference(all_vars, m_params));

		mk_exists_forall_farkas(m_acc_subst, vars, farkas_cons, true, all_lambda_kinds);
		int max_lambda = 2;
		mk_bilin_lambda_constraint(all_lambda_kinds, max_lambda, lambda_cons);

		smt_params new_param;
		smt::kernel solver(m, new_param);
		solver.assert_expr(m.mk_and(farkas_cons, m.mk_and(lambda_cons, m_extras)));

		if (solver.check() == l_true){
			model_ref modref;
			solver.get_model(modref);
			expr_ref instance(m);

			func_decl2params_body::iterator it = m_map.begin();
			func_decl2params_body::iterator end = m_map.end();
			for (; it != end; ++it) {
				if (modref.get()->eval(it->get_value().second, instance)) {
					m_rel_template_instances.insert(it->m_key, instance);
				}
				else {// when does this happen?
					throw(it->m_key->get_decl()->get_name());
				}
			}
		}
		throw(fml);
	}

	expr* get_templat_instance(app* temp_head){
		func_decl2inst::obj_map_entry* e = m_rel_template_instances.find_core(temp_head);
		return e->get_data().m_value;
	}
};

expr_ref rel_template::subst_template_body(expr_ref fml, func_decl2params_body map){
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
			func_decl2params_body::obj_map_entry* e = map.find_core(to_app(fml));
			if (!e) return fml;
			return expr_ref(e->get_data().get_value().second, m);
		}
	}
	return new_formula;
}