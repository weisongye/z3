/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    bound_info.cpp

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-01-17.

--*/
#include"bound_info.h"
#include"ast_pp.h"

bool bound_info::collect_literals(expr * e, expr_ref_buffer & lits ) {
    if (m_m.is_or(e)) {
        lits.append(to_app(e)->get_num_args(), to_app(e)->get_args());
    }
    else {
        lits.push_back(e);
    }
    return true;
}

bool bound_info::get_var_monomial(expr * e, expr_ref & var, expr_ref & coeff) {
    bool foundVar = false;
    if (is_var(e)) {
        var = to_var(e);
        rational val(1, 1);
        coeff = m_au.mk_numeral(val, true);
        foundVar = true;
    }
    else if (m_au.is_mul(e)) {
        if (m_au.is_numeral(to_app(e)->get_arg(0)) && is_var(to_app(e)->get_arg(1))) {
            var = to_app(e)->get_arg(1);
            coeff = to_app(e)->get_arg(0);
            foundVar = true;
        }
    }
    if (foundVar && to_var(var)->get_idx() < m_q->get_num_decls()) {
        return true;
    }
    else {
        TRACE("bound-info-debug",tout << "failed to find monomial " << mk_pp(e, m_m) << "\n";);
        return false;
    }
}

bool bound_info::is_ground_bnd_vars(expr * e) {
    if (is_ground(e)) {
        return true;
    }
    else {
        if (is_var(e)) {
            //if variable is bound by this quantifier and we have not yet found a bounding range for it
            if (to_var(e)->get_idx() >= m_q->get_num_decls() || m_var_order.contains(to_var(e)->get_idx())) {
                return true;
            }
        }
        else if (is_app(e)) {
            for (unsigned i = 0; i < to_app(e)->get_num_args(); i++) {
                if (!is_ground_bnd_vars(to_app(e)->get_arg(i))) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }
}

void bound_info::get_bv_auto_bound(bool isLower, bool isSigned, sort * s, expr_ref & result) {
    result = isLower ? (isSigned ? m_bvu.mk_signed_min(s) : m_bvu.mk_numeral(rational(0),s)) :
                       (isSigned ? m_bvu.mk_signed_max(s) : m_bvu.mk_unsigned_max(s));
}

void bound_info::is_bounded_quantifier_iter(expr_ref_buffer & lits, expr_ref_buffer & bnds, sbuffer<unsigned> & new_bnd_vars, expr_ref_buffer & new_bnds, 
                                            sbuffer<unsigned> & new_bnds_from_vars, sbuffer<bool> & new_bnds_signs,
                                            expr_ref_buffer & new_ovf) {
    for (unsigned i = 0; i < lits.size(); i++) {
        expr * ec = lits[i];
        //if not already formulated as a bound
        if (!bnds.contains(ec)) {
            TRACE("bound-info-debug",tout << "check literal " << mk_pp(ec, m_m) << "\n";);
            //look to see if ec specifies a bound
            bool neg = false;
            if (m_m.is_not(ec)) {
                neg = true;
                ec = to_app(ec)->get_arg(0);
            }
            //arithmetic bound
            if (m_au.is_le(ec) || m_au.is_ge(ec) || m_au.is_lt(ec) || m_au.is_gt(ec)) {
                bool foundVar = false;
                expr_ref var(m_m);
                expr_ref coeff(m_m);
                expr_ref val(m_m);
                val = to_app(ec)->get_arg(1);
                if (m_au.is_add(to_app(ec)->get_arg(0))) {
                    app * ac = to_app(to_app(ec)->get_arg(0));
                    expr_ref_buffer erv(m_m);
                    //take first unbound variable
                    for (unsigned j = 0; j < ac->get_num_args(); j++) {
                        if (!foundVar && get_var_monomial(ac->get_arg(j), var, coeff) && !m_var_order.contains(to_var(var)->get_idx())) {
                            foundVar = true;
                        }
                        else {
                            erv.push_back(ac->get_arg(j));
                        }
                    }
                    //isolate the term
                    if (!erv.empty()) {
                        expr_ref lval(m_m);
                        lval = erv.size()>1 ? m_au.mk_add(ac->get_num_args()-1,erv.c_ptr()) : erv[0];
                        val = m_au.mk_sub(val, lval);
                    }
                }
                else if (get_var_monomial(to_app(ec)->get_arg(0), var, coeff)){
                    //it is a single variable monomial
                    foundVar = true;
                }
                //if found potential variable
                if (foundVar) {
                    //if the value is ground w.r.t already bound vars
                    if (is_ground_bnd_vars(val)) {
                        TRACE("bound-info-debug",tout << "from " << mk_pp(ec, m_m) << ", we have: \n" << mk_pp(coeff, m_m) << " * " << mk_pp(var, m_m) << " ~ " << mk_pp(val, m_m) << "\n";);
                        unsigned id = to_var(var)->get_idx();
                        bool isLower = (neg==(m_au.is_ge(ec) || m_au.is_gt(ec)));
                        //modify based on coefficient sign
                        rational val_r;
                        if (m_au.is_numeral(coeff, val_r)){
                            if (val_r.is_neg()) {
                                TRACE("bound-info-debug",tout << "modify negative coefficient\n";);
                                val_r.neg();
                                coeff = m_au.mk_numeral(val_r, true);
                                val = m_au.mk_mul(m_au.mk_numeral(rational(-1, 1), true), val); 
                                isLower = !isLower;
                            }
                            //modify based on coeff!=1
                            if (coeff != m_au.mk_numeral(rational(1, 1), true)) {
                                TRACE("bound-info-debug",tout << "modify coeff!=1\n";);
                                expr_ref val_div(m_m);
                                val_div = m_au.mk_idiv(val, coeff);
                                if (isLower==neg) {   //if non-strict lower bound or strict upper bound, might need to add one
                                    val = m_au.mk_add(val_div, m_m.mk_ite(m_m.mk_eq(m_au.mk_mod(val,coeff), m_au.mk_numeral(rational(0, 1), true)), 
                                                                          m_au.mk_numeral(rational(0, 1), true),
                                                                          m_au.mk_numeral(rational(1, 1), true)));
                                }
                                else {
                                    val = val_div;
                                }
                            }
                            //modify based on strict inequality
                            if (neg==(m_au.is_lt(ec) || m_au.is_gt(ec))) {
                                TRACE("bound-info-debug",tout << "modify strict\n";);
                                val = m_au.mk_add(val, m_au.mk_numeral(rational(isLower ? 1 : -1, 1), true));
                            }
                            expr_ref_buffer& b = isLower ? m_l : m_u;
                            expr_ref_buffer& bo = isLower ? m_u : m_l;
                            //if the bound has not already been set
                            bool alreadySet = false;
                            if (b[id]) {
                                alreadySet = true;
                                TRACE("bound-info-debug",tout << "modify for preexisting\n";);
                                expr_ref cond(m_m);
                                //make min (or max) term
                                cond = isLower ? m_au.mk_ge(val, b[id]) : m_au.mk_le(val, b[id]);
                                val = m_m.mk_ite(cond, val, b[id]);
                            }
                            //set the bound
                            b.setx(id, val);    //is this how to set?
                            //add to list of bounds
                            new_bnds.push_back(lits[i]);
                            new_bnds_from_vars.push_back(id);
                            new_bnds_signs.push_back(false);
                            new_ovf.push_back(0);
                            //add variable to new bound variables, if now both bounds are set
                            if (!alreadySet && bo[id]) {
                                TRACE("bound-info-debug",tout << "found bound for variable : " << mk_pp(var, m_m) << "\n";);
                                new_bnd_vars.push_back(id);
                            }
                        }
                    }
                    else {
                        TRACE("bound-info-debug",tout << "bound is not ground " << mk_pp(val, m_m) << "\n";);  
                    }
                }
                else {
                    TRACE("bound-info-debug",tout << "could not find variable for " << mk_pp(ec, m_m) << "\n";);
                }
            }
            else if (m_bvu.is_bv_sle(ec) || m_bvu.is_bv_ule(ec) || m_bvu.is_bv_sge(ec) || m_bvu.is_bv_uge(ec)) {      //bit-vector bounds
                app * ac = to_app(ec);
                for (unsigned j = 0; j < ac->get_num_args(); j++ ) {
                    if (is_var(ac->get_arg(j))) {
                        //if (!is_bound(to_var(ac->get_arg(j))->get_idx())) {
                        if (!m_var_order.contains(to_var(ac->get_arg(j))->get_idx())) {
                            unsigned id = to_var(ac->get_arg(j))->get_idx();
                            bool isLower = (j==1)==neg;
                            isLower = (m_bvu.is_bv_sle(ec) || m_bvu.is_bv_ule(ec)) ? isLower : !isLower;
                            bool isSigned = m_bvu.is_bv_sle(ec) || m_bvu.is_bv_sge(ec);
                            bool isStrict = !neg;
                            expr_ref_buffer& b = isLower ? (isSigned ? m_sl : m_l) : (isSigned ? m_su : m_u);
                            expr_ref_buffer& bo = isLower ? (isSigned ? m_su : m_u) : (isSigned ? m_sl : m_l);
                            expr_ref val(m_m);
                            val = ac->get_arg(j==0 ? 1 : 0);
                            //if the value is ground w.r.t already bound vars
                            if (is_ground_bnd_vars(val)) {
                                sort * s = get_sort(ac->get_arg(j));
                                //modify based on strict inequality
                                if (isStrict) {
                                    //must account for overflow
                                    expr_ref ovf(m_m);
                                    ovf = isLower ? (isSigned ? m_bvu.mk_signed_max(s) : m_bvu.mk_unsigned_max(s)) :
                                                    (isSigned ? m_bvu.mk_signed_min(s) : m_bvu.mk_numeral(rational(0),s));
                                    //store in overflow constraints vector
                                    new_ovf.push_back(m_m.mk_eq(val, ovf));
                                    TRACE("bound-info-debug",tout << "modify strict\n";);
                                    val = isLower ? m_bvu.mk_bv_add(val, m_bvu.mk_numeral(rational(1),s)) :
                                                    m_bvu.mk_bv_sub(val, m_bvu.mk_numeral(rational(1),s));
                                }
                                else {
                                    //no overflow constraint
                                    new_ovf.push_back(0);
                                }
                                if (b[id]) {
                                    //check if it is the auto-bound
                                    expr_ref eauto(m_m);
                                    get_bv_auto_bound(isLower, isSigned, s, eauto);
                                    if (b[id]!=eauto) {
                                        TRACE("bound-info-debug",tout << "modify for preexisting\n";);
                                        //duplicate?
                                        expr_ref cond(m_m);
                                        //make min (or max) term
                                        expr * e1 = isLower ? b[id] : val;
                                        expr * e2 = isLower ? val : b[id];
                                        cond = isSigned ? m_bvu.mk_sle(e1, e2) : m_bvu.mk_ule(e1, e2);
                                        val = m_m.mk_ite(cond, val, b[id]);
                                    }
                                }
                                //set the bound
                                b.setx(id, val);
                                //add to list of bounds
                                new_bnds.push_back(lits[i]);
                                new_bnds_from_vars.push_back(id);
                                new_bnds_signs.push_back(isSigned);
                                //if not done so already, auto-set the other bound
                                // [Leo]: This kind of code is not easy to maintain. Does "false" mean no bound?!?
                                if (!bo[id]) {
                                    TRACE("bound-info-debug",tout << "found bound for variable : " << mk_pp(ac->get_arg(j), m_m) << "\n";);
                                    expr_ref auto_bound(m_m);
                                    get_bv_auto_bound(!isLower, isSigned, s, auto_bound);
                                    bo.setx(id, auto_bound);
                                    new_bnd_vars.push_back(id);
                                }
                                break;
                            }
                        }
                    }
                }
            }
        }
    }
}

bool bound_info::compute() {
    if (m_q->is_forall()) {
        TRACE("bound-info",tout << "compute bound info for " << mk_pp(m_q, m_m) << "\n";);
        bool properSorts = true;
        for (unsigned i = 0; i < m_q->get_num_decls(); i++) {
            sort * s = m_q->get_decl_sort(i);
            //check sort is uninterpreted/int/bv
            if (m_m.is_uninterp(s)){
                //uninterpreted sorts are by default bound
                m_var_order.push_back(m_q->get_num_decls()-i-1);
            }
            else if (!m_au.is_int(s) && !m_bvu.is_bv_sort(s)) {
                TRACE("bound-info-debug",tout << "Bound info not supported for sort " << mk_pp(s, m_m) << "\n";);
                properSorts = false;
            }
        }
        if (properSorts) {
            //collect literals from body of quantifier
            expr_ref_buffer lits(m_m);
            //only consider forall?
            if (collect_literals(m_q->get_expr(), lits)) {
                expr_ref_buffer bnds(m_m);
                sbuffer<unsigned> new_bnd_vars;
                expr_ref_buffer new_bnds(m_m);
                sbuffer<unsigned> new_bnds_from_vars;
                sbuffer<bool> new_bnds_signs;
                expr_ref_buffer new_ovf(m_m);
                bool iter_success;
                do {
                    iter_success = false;
                    if (m_var_order.size() < m_q->get_num_decls()) {
                        is_bounded_quantifier_iter(lits, bnds, new_bnd_vars, new_bnds, new_bnds_from_vars, new_bnds_signs, new_ovf);
                        //if necessary, add trivial bv bound
                        if (new_bnd_vars.empty()) {
                            for (unsigned i = 0; i < m_q->get_num_decls(); i++) {
                                sort * s = m_q->get_decl_sort(m_q->get_num_decls()-i-1);
                                if (m_bvu.is_bv_sort(s) && !is_bound(i)) {
                                    var * v = m_m.mk_var(i, s);
                                    TRACE("bound-info-debug",tout << "add trivial bound for bv variable : " << mk_pp(v,m_m) << "\n";);
                                    expr_ref auto_l(m_m);
                                    expr_ref auto_u(m_m);
                                    get_bv_auto_bound(true, false, s, auto_l);
                                    get_bv_auto_bound(false, false, s, auto_u);
                                    m_l.setx(i, auto_l);
                                    m_u.setx(i, auto_u);
                                    new_bnd_vars.push_back(i);
                                    break;
                                }
                            }
                        }
                        //add new_bnd_vars to bnd_vars
                        if (!new_bnd_vars.empty()) {
                            //we add one variable per round, preferring the maximum variable (i.e. the first variable in the quantifier prefix)
                            unsigned max_var = UINT_MAX;
                            unsigned max_non_triv_var = UINT_MAX;
                            for (unsigned i = 0; i < new_bnd_vars.size(); i++) {
                                if (max_var == UINT_MAX || new_bnd_vars[i] > max_var) {
                                    max_var = new_bnd_vars[i];
                                }
                                if (!is_trivial(new_bnd_vars[i]) && (max_non_triv_var == UINT_MAX || new_bnd_vars[i] > max_non_triv_var)) {
                                    max_non_triv_var = new_bnd_vars[i];
                                }
                            }
                            TRACE("bound-info-debug",tout << "Max vars found : " << max_var << " " << max_non_triv_var << "\n";);
                            max_var = max_non_triv_var == UINT_MAX ? max_var : max_non_triv_var;
                            //add to variables
                            m_var_order.push_back(max_var);
                            //check if signed or unsigned (require both unsigned to be set)
                            bool isSigned = (!m_l[max_var] || !m_u[max_var]);
                            TRACE("bound-info",tout << "Bound variable : " << max_var << ", signed = " << isSigned << "\n";);
                            //now, only take the bounds from max_var
                            for (unsigned i = 0; i < new_bnds_from_vars.size(); i++) {
                                if (new_bnds_from_vars[i] == max_var && new_bnds_signs[i] == isSigned) {
                                    TRACE("bound-info",tout << "Processed literal : " << mk_pp(new_bnds[i], m_m) << "\n";);
                                    bnds.push_back(new_bnds[i]);
                                    //check if it has a corresponding overflow constraint, if so, add it to the body
                                    if (new_ovf[i]) {
                                        m_body.push_back(new_ovf[i]);
                                    }
                                }
                            }
                            //clear unused bounds created on this iteration
                            for (unsigned i = 0; i < m_q->get_num_decls(); i++) {
                                // [Leo]: Are you using "false" to mark that we don't have a bound?
                                // [Leo]: Why not 0?
                                if (!m_var_order.contains(i)) {
                                    m_l.setx(i, 0);
                                    m_u.setx(i, 0);
                                    m_sl.setx(i, 0);
                                    m_su.setx(i, 0);
                                }
                                else if (i == max_var ){
                                    if (isSigned) {
                                        m_l.setx(i, 0);
                                        m_u.setx(i, 0);
                                    }
                                    else {
                                        m_sl.setx(i, 0);
                                        m_su.setx(i, 0);
                                    }
                                }
                            }
                            iter_success = true;
                        }
                        //reset temporary information
                        new_bnd_vars.reset();
                        new_bnds.reset();
                        new_bnds_from_vars.reset();
                        new_bnds_signs.reset();
                        new_ovf.reset();
                        TRACE("bound-info-debug",tout << "next level...";);
                    }
                } while (iter_success);
                //push back all literals that did not contribute to bounds to body
                if (m_var_order.size() == m_q->get_num_decls()) {
                    //make new body (all literals that were not processed as bounds)
                    for (unsigned i = 0; i < lits.size(); i++) {
                        if (!bnds.contains(lits[i])) {
                            m_body.push_back(lits[i]);
                        }
                    }
                    m_is_valid = true;
                    TRACE("bound-info-debug", display( tout ););
                    return true;
                }
            }
        }
        else {
            TRACE("bound-info-debug",tout << "Could not find bounds, improper sort for variables\n";);
        }
    }
    return false;
}

void bound_info::display(std::ostream & out) {
    out << "Quantifier " << mk_pp(m_q, m_m) << " has the following bounds : \n";
    for (unsigned i=0; i<m_var_order.size(); i++) {
        int var_index = m_var_order[i];
        sort * s = m_q->get_decl_sort(m_q->get_num_decls()-var_index-1);
        if (!m_m.is_uninterp(s)) {
            expr_ref_buffer & bl = m_l;
            expr_ref_buffer & bu = m_u;
            if (is_bv_signed_bound(var_index)) {
                out << "(signed) ";
                bl = m_sl;
                bu = m_su;
            }
            out << mk_pp(bl[var_index], m_m) << "   <=   " << m_q->get_decl_name(m_q->get_num_decls()-var_index-1) << "   <=   " << mk_pp(bu[var_index], m_m) << "\n";
        }
    }
    expr_ref body_expr(m_m);
    get_body(body_expr, false);
    out <<  "Body : " << mk_pp(body_expr, m_m) << "\n\n";
}

bool bound_info::is_bound(unsigned idx){
    sort * s = m_q->get_decl_sort(idx);
    if (m_m.is_uninterp(s)) {
        return true;
    }
    else if (m_au.is_int(s)) {
        return is_int_bound(idx);
    }
    else if (m_bvu.is_bv_sort(s)) {
        return is_bv_signed_bound(idx) || is_bv_unsigned_bound(idx);
    }
    else {
        return false;
    }
}

bool bound_info::is_normalized() {
    for (unsigned i = 0; i < m_q->get_num_decls(); i++) {
        if (!is_normalized(i)) {
            return false;
        }
    }
    return true;
}

bool bound_info::is_normalized(unsigned idx) {
    if (is_bv_signed_bound(idx)) {
        TRACE("bound-info-debug-norm",tout << "Bound is not normalized, contains signed bound.";);
        return false;
    }
    else{
        expr_ref lower(m_m);
        lower = get_lower_bound(idx);
        sort * s = m_q->get_decl_sort(m_q->get_num_decls()-1-idx);
        if ( m_m.is_uninterp(s) || 
             (m_au.is_int(s) && lower == m_au.mk_numeral(rational(0, 1), true)) ||
             (m_bvu.is_bv_sort(s) && lower == m_bvu.mk_numeral(rational(0), s)) ) {
            //lower bound is zero
        }
        else{
            TRACE("bound-info-debug-norm",tout << "Bound is not normalized: " << mk_pp(lower, m_m) << "   <=   " << m_q->get_decl_name(m_q->get_num_decls()-idx-1) << "\n";);
            return false;
        }
        return true;
    }
}

bool bound_info::is_trivial(unsigned idx) {
    if (!is_bound(idx)) {
        return true;
    }
    else {
        sort * s = m_q->get_decl_sort(idx);
        //check if it is not trivial first
        if (m_bvu.is_bv_sort(s)) {
            expr_ref auto_l(m_m);
            expr_ref auto_u(m_m);
            bool isSigned = is_bv_signed_bound(idx);
            get_bv_auto_bound(true, isSigned, s, auto_l);
            get_bv_auto_bound(false, isSigned, s, auto_u);
            if (isSigned) {
                return (m_sl[idx]==auto_l && m_su[idx]==auto_u);
            } 
            else {
                return (m_l[idx]==auto_l && m_u[idx]==auto_u);
            }
        }
        return false;
    }
}

void bound_info::get_body(expr_ref& body, bool inc_bounds){
    if (m_is_valid) {
        expr_ref_buffer lits(m_m);
        if (inc_bounds) {
            for (unsigned i = 0; i < m_var_order.size(); i++) {
                int index = m_var_order[i];
                sort * s = m_q->get_decl_sort(m_q->get_num_decls()-1-index);
                var * v = m_m.mk_var(index, s);
                if (m_au.is_int(s)) {
                    lits.push_back(m_m.mk_not(m_au.mk_ge(v, m_l[index])));
                    lits.push_back(m_m.mk_not(m_au.mk_le(v, m_u[index])));
                }
                else if (m_bvu.is_bv_sort(s)) {
                    if (is_bv_unsigned_bound(index)) {
                        lits.push_back(m_m.mk_not(m_bvu.mk_ule(m_l[index],v)));
                        lits.push_back(m_m.mk_not(m_bvu.mk_ule(v, m_u[index])));
                    }
                    else {
                        lits.push_back(m_m.mk_not(m_bvu.mk_sle(m_sl[index],v)));
                        lits.push_back(m_m.mk_not(m_bvu.mk_sle(v, m_su[index])));
                    }
                }
            }
        }
        lits.append(m_body.size(),m_body.c_ptr());
        body = lits.size()>1 ? m_m.mk_or(lits.size(), lits.c_ptr()) : (lits.size()==1 ? lits[0] : m_m.mk_true());
    } 
    else {
        body = m_q->get_expr();
    }
}

quantifier* bound_info::get_quantifier() {
    expr_ref body(m_m);
    get_body(body);
    return m_m.update_quantifier(m_q, body);
}

unsigned bound_info::get_var_order_index(unsigned idx) {
    for (unsigned i = 0; i < m_var_order.size(); i++) {
        if (m_var_order[i] == idx) {
            return i;
        }
    }
    return UINT_MAX;
}

// [Leo]: This method does not belong here.
void bound_info::apply_rewrite(th_rewriter& rw) {
    for (unsigned i = 0; i < m_l.size(); i++ ) {
        expr_ref result(m_m);
        if (m_l[i]) {
            rw(m_l[i],result);
            m_l.setx(i, result);
        }
        if (m_u[i]) {
            rw(m_u[i],result);
            m_u.setx(i, result);
        }
        if (m_sl[i]) {
            rw(m_sl[i],result);
            m_sl.setx(i, result);
        }
        if (m_su[i]) {
            rw(m_su[i],result);
            m_su.setx(i, result);
        }
    }
}
