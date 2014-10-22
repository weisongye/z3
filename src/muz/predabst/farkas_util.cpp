
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

vector<expr_ref_vector> cnf_to_dnf2(vector<vector<expr_ref_vector>> cnf_sets, ast_manager& m){

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
			vector<vector<expr_ref_vector>> dnf_sub_formulas;
			sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());

			for (unsigned i = 0; i < sub_formulas.size(); ++i) {
				dnf_sub_formulas.push_back(to_dnf_struct(expr_ref(sub_formulas[i].get(), m)));
			}
			dnf_formula = cnf_to_dnf2(dnf_sub_formulas, m);
		}
		else if (m.is_or(fml)){
			expr_ref_vector sub_formulas(m);
			vector<vector<expr_ref_vector>> dnf_sub_formulas;
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

bool well_founded(expr_ref_vector vs, expr_ref_vector ws, expr_ref& LHS, expr_ref_vector& values){
	ast_manager& m = LHS.get_manager();
	reg_decl_plugins(m);
	arith_util arith(m);

	SASSERT(!m.is_true(LHS));
	SASSERT(m.is_and(LHS));

	//SASSERT(LHS.get_num_args() > 1);
	SASSERT(vs.size() == ws.size());

	expr_ref_vector params(m);

	expr_ref sum_psvs(arith.mk_numeral(rational(0), true), m);
	expr_ref sum_psws(arith.mk_numeral(rational(0), true), m);

	expr_ref delta0(m.mk_const(symbol("delta0"), arith.mk_int()), m);
	params.push_back(delta0);

	//std::cout << "vs " << vs.size() << "\n";
	for (unsigned i = 0; i < vs.size(); ++i) {
		expr_ref param(m.mk_fresh_const("p", arith.mk_int()), m);

		params.push_back(param);
		sum_psvs = arith.mk_add(sum_psvs.get(), arith.mk_mul(param.get(), vs[i].get()));
		sum_psws = arith.mk_add(sum_psws.get(), arith.mk_mul(param.get(), ws[i].get()));
	}

	expr_ref bound(arith.mk_ge(sum_psvs, delta0), m);
	expr_ref decrease(arith.mk_lt(sum_psws, sum_psvs), m);

	//expr_ref to_solve(m.mk_implies(LHS.get(), m.mk_and(bound.get(), decrease.get())), m);
	expr_ref to_solve(m.mk_or(m.mk_not(LHS), m.mk_and(bound, decrease)), m);

	expr_ref_vector vars(vs);
	vars.append(ws);

	expr_ref constraint_st(m.mk_true(), m);
	if (exists_valid(to_solve, vars, constraint_st)) {
		smt_params new_param;;
		smt::kernel solver(m, new_param);
		solver.assert_expr(constraint_st);

		if (solver.check() == l_true){
			model_ref modref;
			solver.get_model(modref);
			expr_ref value(m);

			expr_ref sum_psvs_sol(arith.mk_numeral(rational(0), true), m);
			expr_ref bound_sol(m);

			for (unsigned j = 0; j < params.size(); j++) {
				if (modref.get()->eval(params[j].get(), value, true)) {
					values.push_back(value);
				}
				else {
					return false;
				}
			}
			return true;
		}
		else {
			return false;
		}

	}
	else{
		return false;
	}

}

