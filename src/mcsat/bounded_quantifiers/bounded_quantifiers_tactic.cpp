/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    bounded_quantifiers_tactic.cpp

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-01-17.

--*/
#include"bounded_quantifiers_tactic.h"
#include"tactic.h"
#include"rewriter_def.h"
#include"var_subst.h"
#include"bound_info.h"
#include"ast_pp.h"
#include"th_rewriter.h"

class normalize_bounded_quantifiers_tactic : public tactic {

    struct rw_cfg : public default_rewriter_cfg {
        ast_manager & m;
        arith_util m_au;
        bv_util m_bvu;
        rw_cfg(ast_manager & _m):m(_m), m_au(m), m_bvu(m){}
        
	    bool reduce_quantifier(quantifier * old_q, 
                               expr * new_body, 
                               expr * const * new_patterns, 
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {
            TRACE("normalize-bound-quant",tout << "Process " << mk_pp(old_q,m) << "\n";);
            quantifier * q = m.update_quantifier(old_q, old_q->get_num_patterns(), new_patterns, old_q->get_num_no_patterns(), new_no_patterns, new_body);
	        bound_info bi(m, m_au, m_bvu, q);
            if (bi.compute()) {
                //bi.print("normalize-bound-quant-debug");
                expr_ref_buffer bound_lits(m);
                expr_ref_buffer body_lits(m);
                //start with all literals from body
                body_lits.append(bi.m_body.size(), bi.m_body.c_ptr());
                //make the substitution we will be using
                expr_ref_buffer subs(m);
                for (unsigned i=0; i<q->get_num_decls(); i++) {
                    sort * s = q->get_decl_sort(i);
                    expr * v = m.mk_var(q->get_num_decls()-1-i, s);
                    subs.push_back(v);
                }
                //substitution object
                var_subst vs(m);
                //normalize each of the bounds
                for (unsigned iv=0; iv<bi.m_var_order.size(); iv++) {
                    unsigned i = bi.m_var_order[iv];
                    sort * s = q->get_decl_sort(q->get_num_decls()-1-i);
                    expr * v = m.mk_var(i, s);
                    //construct lower and upper bounds (must apply current substitution to them)
                    expr_ref lower(m);
                    expr_ref upper(m);
                    vs(bi.get_lower_bound(i), subs.size(), subs.c_ptr(), lower);
                    vs(bi.get_upper_bound(i), subs.size(), subs.c_ptr(), upper);
                    expr_ref subs_val(m);
                    //add normalized bounds to bound_lits
                    if (m_au.is_int(s)) {
                        bound_lits.push_back(m.mk_not(m_au.mk_ge(v, m_au.mk_numeral(rational(0), true))));
                        bound_lits.push_back(m.mk_not(m_au.mk_le(v, m_au.mk_sub(upper, lower))));
                        subs_val = m_au.mk_add(v, lower);
                    }
                    else if (m_bvu.is_bv_sort(s)) {
                        unsigned sz = m_bvu.get_bv_size(s);
                        bound_lits.push_back(m.mk_not(m_bvu.mk_ule(m_bvu.mk_numeral(rational(0), sz),v)));
                        bound_lits.push_back(m.mk_not(m_bvu.mk_ule(v, m_bvu.mk_bv_sub(upper, lower))));
                        //additionally, body is satisfied when lower > upper
                        bound_lits.push_back(m.mk_not(bi.is_bv_signed_bound(i) ? m_bvu.mk_sle(lower, upper) :
                                                                                 m_bvu.mk_ule(lower, upper)));
                        subs_val = m_bvu.mk_bv_add(v, lower);
                    }
                    //also add v -> (v+l) to the substitution
                    TRACE("normalize-bound-quant-debug",tout << "Substitution value for variable " << i << " is " << mk_pp(subs_val,m) << "\n";);
                    subs.setx(q->get_num_decls()-1-i, subs_val);
                }
                //apply substitution to each of the body literals
                for (unsigned i=0; i<body_lits.size(); i++) {
                    expr_ref bd_res(m);
                    vs(body_lits[i], subs.size(), subs.c_ptr(), bd_res);
                    body_lits.setx(i, bd_res);
                }
                //construct the body (it is an "or" of all the literals)
                bound_lits.append(body_lits.size(), body_lits.c_ptr());
                result = m.update_quantifier(q, m.mk_or(bound_lits.size(), bound_lits.c_ptr()));
                TRACE("normalize-bound-quant",tout << "Normalized " << mk_pp(old_q,m) << " to \n     " << mk_pp(result,m) << "\n";);
                /* (test if the next bounds found are indeed normalized)
                bound_info bi2(m, m_au, m_bvu, to_quantifier(result));
                if( bi2.compute()){
                    bi2.print("");
                }
                */
	            return true;
            }
            return false;
        }
    };

    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;
        rw(ast_manager & m):
            rewriter_tpl<rw_cfg>(m, false, m_cfg),
            m_cfg(m) {
        }
    };
    
    rw            m_rw;
    params_ref    m_params;
public:
    normalize_bounded_quantifiers_tactic(ast_manager & m, params_ref const & p):
	m_rw(m),
	m_params(p) {
    }

    virtual tactic * translate(ast_manager & m) {
	return alloc(normalize_bounded_quantifiers_tactic, m, m_params);
    }

    virtual ~normalize_bounded_quantifiers_tactic() {}

    virtual void updt_params(params_ref const & p) { m_params = p; }

    virtual void collect_param_descrs(param_descrs & r) { }

    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        TRACE("normalize_bounded_quantifiers", tout << "params: " << m_params << "\n"; g->display(tout););
	    fail_if_proof_generation("normalize_bounded_quantifiers_tactic", g);
	    ast_manager & m = g->m();
        SASSERT(g->is_well_sorted());
        mc = 0; pc = 0; core = 0;
        tactic_report report("normalize_bounded_quantifiers", *g);
        unsigned sz = g->size();
	    expr_ref new_curr(m);
        for (unsigned i = 0; i < sz; i++) {
            expr * curr = g->form(i);
	        m_rw(curr, new_curr);
            g->update(i, new_curr, 0, g->dep(i));
        }
        g->inc_depth();
        result.push_back(g.get());
        TRACE("normalize_bounded_quantifiers", g->display(tout););
        SASSERT(g->is_well_sorted());
    }
    
    virtual void cleanup() {
	    m_rw.cleanup();
    }

    virtual void set_cancel(bool f) {
	    m_rw.set_cancel(f);
    }
};


tactic * mk_normalize_bounded_quantifiers_tactic(ast_manager & m, params_ref const & p) {
  std::cout << "mk_normalize_bounded_quantifiers_tactic\n";
  return alloc(normalize_bounded_quantifiers_tactic, m, p);
}

class minimize_bounded_quantifiers_tactic : public tactic {
    struct rw_cfg : public default_rewriter_cfg {
        ast_manager & m_m;
        arith_util m_au;
        bv_util m_bvu;
        rw_cfg(ast_manager & _m):m_m(_m), m_au(_m), m_bvu(_m){}
        
        bool get_monomial( expr * e, expr_ref_buffer & terms, sbuffer<int> & vars, expr_ref_buffer & coeff ) {
            //TODO
            return false;
        }
	    bool reduce_quantifier(quantifier * old_q, 
                               expr * new_body, 
                               expr * const * new_patterns, 
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {
            TRACE("minimize-bound-quant",tout << "Process " << mk_pp(old_q,m_m) << "\n";);
            quantifier * q = m_m.update_quantifier(old_q, old_q->get_num_patterns(), new_patterns, old_q->get_num_no_patterns(), new_no_patterns, new_body);
	        bound_info bi(m_m, m_au, m_bvu, q);
            if (bi.compute()) {
                //check that all lower bounds are zero
                if (bi.is_normalized()) {
                    bool iter_succ = true;
                    do {
                        iter_succ = false;
                        //over-approximation of lower/upper bounds (these are ground)
                        expr_ref_buffer abs_lower(m_m);
                        expr_ref_buffer abs_upper(m_m);
                        //iterate over all bounds to see if they can propagate lower or upper bounds
                        for (unsigned i=1; i<bi.m_var_order.size(); i++) {
                            int prop_index = bi.m_var_order[i];
                            //process upper bound into u = t + c1*x1 + ... + cn*xn
                            expr_ref_buffer terms(m_m);
                            sbuffer<int> vars;
                            expr_ref_buffer coeffs(m_m);
                            if (get_monomial(bi.get_upper_bound(prop_index), terms, vars, coeffs)) {
                                //get upper/lower bounds for each of these variables
                                expr_ref_buffer var_lower(m_m);
                                expr_ref_buffer var_upper(m_m);
                                for (unsigned j = 0; j < vars.size(); j++ ) {
                                    int id = bi.get_var_order_index(vars[j]);
                                    if (id>=0) {
                                        var_lower.push_back(abs_lower[id]);
                                        var_upper.push_back(abs_upper[id]);
                                    }
                                    else {
                                        var_lower.push_back(m_m.mk_false());
                                        var_upper.push_back(m_m.mk_false());
                                    }
                                }
                                //try to isolate each x1 .... xn, and propagate the corresponding bound
                                for (unsigned v = 0; v < vars.size(); v++) {
                                    //isolating xi
                                    int var_index = vars[v];
                                    sort * sv = q->get_decl_sort(q->get_num_decls()-1-var_index);
                                    rational cv;
                                    unsigned bvszv;
                                    if ((m_au.is_int(sv) && m_au.is_numeral(coeffs[v],cv)) || 
                                        (m_bvu.is_bv_sort(sv) && m_bvu.is_numeral(coeffs[v],cv,bvszv))) {
                                        //will be generating a lower bound if coefficient for vars[v] is negative
                                        bool isLower = cv.is_neg();
                                        //values we will use for each of variables x1...xn
                                        expr_ref_buffer values(m_m);
                                        //find values for x1...x{v-1} x{v+1}...xn to maximize/minimize u
                                        for (unsigned j = 0; j < vars.size(); j++ ) {
                                            sort * ss = q->get_decl_sort(q->get_num_decls()-1-vars[j]);
                                            //get the corresponding upper or lower bound 
                                            if (j!=var_index) {
                                                rational cs;
                                                unsigned bvszs;
                                                if ((m_au.is_int(ss) && m_au.is_numeral(coeffs[j], cs)) || 
                                                    (m_bvu.is_bv_sort(ss) && m_bvu.is_numeral(coeffs[j], cs, bvszs))) {
                                                    if (isLower==cs.is_neg()) {
                                                        //substitute maximum value
                                                        values.push_back(var_upper[j]);
                                                    }
                                                    else {
                                                        //substitute minimum value
                                                        values.push_back(var_lower[j]);
                                                    }
                                                }
                                            }
                                            else {
                                                values.push_back(m_m.mk_var(vars[j], ss));
                                            }
                                        }
 
                                        //now construct the new upper/lower bound
                                        expr_ref_buffer new_bound_vec(m_m);
                                        new_bound_vec.append(terms.size(),terms.c_ptr());
                                        for (unsigned j = 0; j < vars.size(); j++) {
                                            if (j!=v) {
                                                if (m_au.is_int(sv)) {
                                                    new_bound_vec.push_back(m_au.mk_mul(coeffs[j], values[j]));
                                                }
                                                else if (m_bvu.is_bv_sort(sv)) {
                                                    new_bound_vec.push_back(m_bvu.mk_bv_mul(coeffs[j], values[j]));
                                                }
                                            }
                                        }
                                        //construct new bound term
                                        expr_ref new_bound(m_m);
                                        new_bound = m_au.is_int(sv) ? m_au.mk_add(new_bound_vec.size(), new_bound_vec.c_ptr()) : m_bvu.mk_bv_add(new_bound_vec.size(), new_bound_vec.c_ptr());
                                        //negate if an upper bound
                                        if (!isLower) {
                                            new_bound = m_au.is_int(sv) ? m_au.mk_sub(m_au.mk_numeral(rational(0),true), new_bound) : m_bvu.mk_bv_sub(m_bvu.mk_numeral(rational(0),sv), new_bound);
                                        }
                                        //we have infered the bound xv ~ new_bound
                                    }
                                }
                                //now construct abs_upper and abs_lower bounds
                             }
                        }
                    } while (iter_succ);
                }
                else {
                    TRACE("minimize-bound-quant",tout << "Bounds are not normalized.\n";);
                }
            }
            return false;
        }
    };
    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;
        rw(ast_manager & m):
            rewriter_tpl<rw_cfg>(m, false, m_cfg),
            m_cfg(m) {
        }
    };
    
    rw            m_rw;
    params_ref    m_params;
public:
    minimize_bounded_quantifiers_tactic(ast_manager & m, params_ref const & p):
	m_rw(m),
	m_params(p) {
    }

    virtual tactic * translate(ast_manager & m) {
	return alloc(minimize_bounded_quantifiers_tactic, m, m_params);
    }

    virtual ~minimize_bounded_quantifiers_tactic() {}

    virtual void updt_params(params_ref const & p) { m_params = p; }

    virtual void collect_param_descrs(param_descrs & r) { }

    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        TRACE("minimize_bounded_quantifiers", tout << "params: " << m_params << "\n"; g->display(tout););
	    fail_if_proof_generation("minimize_bounded_quantifiers_tactic", g);
	    ast_manager & m = g->m();
        SASSERT(g->is_well_sorted());
        mc = 0; pc = 0; core = 0;
        tactic_report report("minimize_bounded_quantifiers", *g);
        unsigned sz = g->size();
	    expr_ref new_curr(m);
        for (unsigned i = 0; i < sz; i++) {
            expr * curr = g->form(i);
	        m_rw(curr, new_curr);
            g->update(i, new_curr, 0, g->dep(i));
        }
        g->inc_depth();
        result.push_back(g.get());
        TRACE("minimize_bounded_quantifiers", g->display(tout););
        SASSERT(g->is_well_sorted());
    }
    
    virtual void cleanup() {
	    m_rw.cleanup();
    }

    virtual void set_cancel(bool f) {
	    m_rw.set_cancel(f);
    }
};

//expand tactic
// parameters should take:
//    int expand_bound:         what bound we should try for integers, bit-vectors
//    int exp_bound_limit:      if bound is already known to be 0 <= x <= n for some variable x and value n, and if n>exp_bound_limit, we fail.
class expand_bounded_quantifiers_tactic : public tactic {
    struct rw_cfg : public default_rewriter_cfg {
    private:
        bool process(bound_info & bi, expr_ref & body, unsigned index, var_subst & vs, expr_ref_buffer & val_subs, expr_ref_buffer & exp_result) {
            if (index==bi.m_var_order.size()) {
                //add body substituted for the values in vals
                expr_ref subs_body(m);
                vs(body, val_subs.size(), val_subs.c_ptr(), subs_body);
                arith_simp(subs_body,subs_body);
                exp_result.push_back(subs_body);
                return true;
            }
            else {
                unsigned i = bi.m_var_order[index];
                sort * s = bi.m_q->get_decl_sort(bi.m_q->get_num_decls()-1-i);
                //calculate the range
                expr_ref upper(m);
                upper = bi.get_upper_bound(i);
                //apply substitution to "upper" based on val_subs
                vs(upper, val_subs.size(), val_subs.c_ptr(), upper);
                //rewrite upper?
                arith_simp(upper,upper);
                //find the constant range
                unsigned range;
                bool success = false;
                if (m_au.is_int(s)) {
                    rational ur;
                    if (m_au.is_numeral(upper, ur)) {
                        //the range is already a constant
                        range = (unsigned)ur.get_uint64();
                        success = true;
                    }
                    else {
                        //the range is the bound we have specified
                        range = m_exp_bound;
                        //must add constraint to result to make it constant
                        expr_ref bnd(m);
                        bnd = m_au.mk_le(upper, m_au.mk_numeral(rational(range), true));
                        //std::cout << "Add constraint " << mk_pp(bnd,m) << std::endl;
                        if (!exp_result.contains(bnd)) {
                            exp_result.push_back(bnd);
                        }
                        success = true;
                    }
                }
                else if (m_bvu.is_bv_sort(s)) {
                    rational ur;
                    unsigned sz;
                    if (m_bvu.is_numeral(upper, ur, sz)) {
                        range = (unsigned)ur.get_uint64();
                        success = true;
                    }
                    else {
                        range = m_exp_bound;
                        //must add constraint to result to make it constant
                        expr_ref bnd(m);
                        bnd = m_bvu.mk_ule(upper, m_bvu.mk_numeral(rational(range), s));
                        if (!exp_result.contains(bnd)) {
                            exp_result.push_back(bnd);
                        }
                        success = true;
                    }
                }
                //if we found a range and it is less than our bound limit
                if (success && range<=m_exp_bound_limit) {
                    //iterate over all values in the range
                    for (unsigned v=0; v<=range; v++) {
                        expr_ref val(m);
                        val = m_au.is_int(s) ? m_au.mk_numeral(rational(v), true) : m_bvu.mk_numeral(rational(v),s);
                        val_subs.setx(bi.m_q->get_num_decls() - 1 - i, val);
                        TRACE("expand-bound-quant-debug", tout << "Consider " << v << " / " << i << "\n";);
                        //check if the body is trivially satisfied?
                        if (!process(bi, body, index+1, vs, val_subs, exp_result)) {
                            return false;
                        }
                    }
                    return true;
                }
                else {
                    TRACE("expand-bound-quant", tout << "Could not process upper bound " << mk_pp(upper,m) << "\n";);
                    return false;
                }
            }
        }
    public:
        ast_manager & m;
        arith_util m_au;
        bv_util m_bvu;
        unsigned m_exp_bound;
        unsigned m_exp_bound_limit;
        params_ref arith_p;
        th_rewriter arith_simp;
        rw_cfg(ast_manager & _m, int exp_bound, int exp_bound_limit):
            m(_m), m_au(m), m_bvu(m), m_exp_bound(exp_bound), m_exp_bound_limit(exp_bound_limit), arith_simp(m,arith_p){
            arith_p.set_bool("sort_sums", true);
        }
	    bool reduce_quantifier(quantifier * old_q, 
                               expr * new_body, 
                               expr * const * new_patterns, 
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {
            TRACE("expand-bound-quant", tout << "Process " << mk_pp(old_q,m) << "\n";);
            quantifier * q = m.update_quantifier(old_q, old_q->get_num_patterns(), new_patterns, old_q->get_num_no_patterns(), new_no_patterns, new_body);
	        bound_info bi(m, m_au, m_bvu, q);
            if (bi.compute()) {
                //check that all lower bounds are zero
                if (bi.is_normalized()) {
                    //we will rewrite the quantifier into a conjunction based on expansion
                    //the values we make for each variable
                    expr_ref_buffer val_subs(m);
                    for (unsigned i=0; i<q->get_num_decls(); i++) {
                        sort * s = q->get_decl_sort(i);
                        expr * v = m.mk_var(q->get_num_decls()-1-i, s);
                        val_subs.push_back(v);
                    }
                    //the variable substitution object
                    var_subst vs(m);
                    //the new body of quantifier (without the bounding literals)
                    expr_ref body(m);
                    //bi.get_body(body);
                    body = q->get_expr();       //should include the entire body for precision
                    //simplify the body
                    arith_simp(body,body);
                    //conjunction of formulas in the result
                    expr_ref_buffer exp_result(m);
                    //now, populate the result buffer
                    if (process(bi, body, 0, vs, val_subs, exp_result)) {
                        //result is a conjunction of the literals in exp_result
                        result = exp_result.size()>1 ? m.mk_and(exp_result.size(), exp_result.c_ptr()) : (exp_result.size()==1 ? exp_result[0] : m.mk_true());
                        TRACE("expand-bound-quant", tout << "Expand, got result " << mk_pp(result,m) << "\n";);
                        //std::cout << "Got result " << mk_pp(result,m) << std::endl;
                        return true;
                    }
                    else {
                        TRACE("expand-bound-quant",tout << "Bound expansion failed.\n";);
                    }
                }
                else {
                    TRACE("expand-bound-quant",tout << "Bounds are not normalized.\n";);
                }
                //std::cout << "Could not process " << mk_pp(q,m) << "\n";
                //bi.print("");
            }
            else {
                TRACE("expand-bound-quant",tout << "Could not find bounds.\n";);
            }
	        return false;
        }
    };
    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;
        rw(ast_manager & m, int exp_bound, int exp_bound_limit):
            rewriter_tpl<rw_cfg>(m, false, m_cfg),
            m_cfg(m, exp_bound, exp_bound_limit) {
        }
    };
    rw            m_rw;
    params_ref    m_params;
public:
    expand_bounded_quantifiers_tactic(ast_manager & m, params_ref const & p):
	m_params(p),
    m_rw(m,expand_bound(),expand_bound_limit()){    //TODO
    }

    virtual tactic * translate(ast_manager & m) {
	    return alloc(expand_bounded_quantifiers_tactic, m, m_params);
    }

    virtual ~expand_bounded_quantifiers_tactic() {}

    virtual void updt_params(params_ref const & p) { m_params = p; }

    virtual void collect_param_descrs(param_descrs & r) { }

    //TODO
    int expand_bound() { return 1; }
    int expand_bound_limit() { return 10; }

    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        TRACE("expand_bounded_quantifiers", tout << "params: " << m_params << "\n"; g->display(tout););
	    fail_if_proof_generation("expand_bounded_quantifiers_tactic", g);
	    ast_manager & m = g->m();
        SASSERT(g->is_well_sorted());
        mc = 0; pc = 0; core = 0;
        tactic_report report("expand_bounded_quantifiers", *g);
        unsigned sz = g->size();
	    expr_ref new_curr(m);
        for (unsigned i = 0; i < sz; i++) {
            expr * curr = g->form(i);
            m_rw(curr, new_curr);
            g->update(i, new_curr, 0, g->dep(i));
        }
        g->inc_depth();
        result.push_back(g.get());
        TRACE("expand_bounded_quantifiers", g->display(tout););
        SASSERT(g->is_well_sorted());
    }
    
    virtual void cleanup() {
	    m_rw.cleanup();
    }

    virtual void set_cancel(bool f) {
	    m_rw.set_cancel(f);
    }
};


tactic * mk_expand_bounded_quantifiers_tactic(ast_manager & m, params_ref const & p) {
  std::cout << "mk_expand_bounded_quantifiers_tactic\n";
  return alloc(expand_bounded_quantifiers_tactic, m, p);
}
