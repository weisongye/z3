/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    eval_check.cpp

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-04-21.

--*/

#include"full_model_check.h"
#include"ast_pp.h"
#include"model_construct.h"
#include"classify_quantifier.h"
#include"model_check.h"

//#define EVAL_CHECK_DEBUG

using namespace qsolver;

value_tuple * value_tuple::mk(mc_context & mc, unsigned arity) {
    //small_object_allocator & allocator = _m.get_allocator();
    void * mem = mc.allocate(sizeof(value_tuple) + arity * sizeof(val*) );
    return new (mem) value_tuple(arity);
}

cond * cond::mk(mc_context & mc, unsigned arity) {
    //small_object_allocator & allocator = _m.get_allocator();
    void * mem  = mc.allocate(sizeof(value_tuple) + arity * sizeof(abs_val*) );
    return new (mem) cond(arity);
}

bool cond::is_value() {
    for (unsigned i=0; i<get_size(); i++) {
        if (!m_vec[i]->is_value()) {
            return false;
        }
    }
    return true;
}

bool cond::is_star() {
    for (unsigned i=0; i<get_size(); i++) {
        if (!m_vec[i]->is_star()) {
            return false;
        }
    }
    return true;
}

bool cond_generalization_trie::has_generalization(mc_context & mc, cond * c, unsigned index, abs_val * star) {
    SASSERT(index<c->get_size());
    abs_val * curr = c->get_value(index);
    cond_generalization_trie * ct;
    if (m_children.find(curr, ct)) {
        if (index==(c->get_size()-1)) {
            return true;
        }
        else if (ct->has_generalization(mc, c, index+1, star)) {
            return true;
        }
    }
    if (star!=curr && m_children.find(star, ct)) {
        return index==(c->get_size()-1) || ct->has_generalization(mc, c, index+1, star);
    }
    else {

        return false;
    }
}

bool cond_generalization_trie::add(mc_context & mc, cond * c, unsigned index, abs_val * star, unsigned data_val) {
    if (index==c->get_size()) {
        if (m_data==0) {
            m_data = data_val+1;
            return true;
        }
        else {
            return false;
        }
    }
    else {
        abs_val * curr = c->get_value(index);
        cond_generalization_trie * ct;
        //first check if it is generalized
        if (star!=curr && m_children.find(star,ct)) {
            if (index==(c->get_size()-1) || ct->has_generalization(mc, c, index+1, star)) {
                return false;
            }
        }
        if (m_children.find(curr, ct)) {
            return ct->add(mc, c, index+1, star, data_val);
        }
        else {
            void * mem = mc.allocate(sizeof(cond_generalization_trie));
            ct = new (mem) cond_generalization_trie;
            m_children.insert(curr, ct);
            return ct->add(mc, c, index+1, star, data_val);
        }
    }
}

bool cond_generalization_trie::add(mc_context & mc, cond * c, unsigned data_val) { 
    return add(mc, c, 0, mc.mk_star(), data_val); 
}

bool cond_generalization_trie::evaluate(mc_context & mc, cond * c, unsigned index, unsigned & data_val) {
    if (index==c->get_size()) {
        if (m_data==0) {
            return false;
        }
        else {
            data_val = m_data-1;
            return true;
        }
    }
    else {
        cond_generalization_trie * ct;
        if (m_children.find(c->get_value(index), ct)) {
            return ct->evaluate(mc, c, index+1, data_val);
        }
        else {
            return false;
        }
    }
}

bool cond_generalization_trie::evaluate(mc_context & mc, ptr_buffer<abs_val> & vals, unsigned index, unsigned & data_val) {
    if (index==vals.size()) {
        if (m_data==0) {
            return false;
        }
        else {
            data_val = m_data-1;
            return true;
        }
    }
    else {
        cond_generalization_trie * ct;
        if (m_children.find(vals[index], ct)) {
            return ct->evaluate(mc, vals, index+1, data_val);
        }
        else {
            return false;
        }
    }
}

bool cond_generalization_trie::evaluate(mc_context & mc, ptr_buffer<val> & vals, unsigned index, unsigned & data_val) {
    if (index==vals.size()) {
        if (m_data==0) {
            return false;
        }
        else {
            data_val = m_data-1;
            return true;
        }
    }
    else {
        cond_generalization_trie * ct;
        if (m_children.find(mc.mk_value(vals[index]), ct)) {
            return ct->evaluate(mc, vals, index+1, data_val);
        }
        else {
            return false;
        }
    }
}

bool def::append_entry(mc_context & mc, cond * c, value_tuple * v) {
    bool has_gen = !m_cgt.add(mc, c, m_conds.size());

    // the unoptimized version:
    /*
    for (int i=(m_conds.size()-1); i>=0; i--) {
        if (mc.is_generalization(m_conds[i],c)) {
            SASSERT(has_gen);
            return true;
        }
    }
    SASSERT(!has_gen);
    return false;
    */
    if (!has_gen) {
        m_conds.push_back(c);
        m_values.push_back(v);
        return true;
    }
    else {
        return false;
    }
}

value_tuple * def::evaluate(mc_context & mc, cond * c, bool ignore_else) {
    SASSERT(!ignore_else);
    //value_tuple * vte = 0;
    unsigned index;
    if (m_cgt.evaluate(mc, c, index)) {
        //vte = m_values[index];
        return m_values[index];
    }
    //unoptimized (or for non-ground)
    for( unsigned i=0; i<m_conds.size(); i++ ){
        if (mc.is_compatible(m_conds[i], c)) {
            //if (vte) {
            //    SASSERT(index==i);
            //}
            return m_values[i];
        }
    }
    return 0;
}

value_tuple * def::evaluate(mc_context & mc, ptr_buffer<val> & vals, bool ignore_else) {
    SASSERT(!ignore_else);
    //value_tuple * vte = 0;
    unsigned index;
    if (m_cgt.evaluate(mc, vals, index)) {
        //vte = m_values[index];
        return m_values[index];
    }
    //unoptimized (or for non-ground)
    for( unsigned i=0; i<m_conds.size(); i++ ){
        if (mc.is_generalization(m_conds[i], vals)) {
            //if (vte) {
            //    SASSERT(index==i);
            //}
            return m_values[i];
        }
    }
    return 0;
}

void def::simplify(mc_context & mc) {
    if (m_has_simplified) {
        TRACE("def_simplify",  tout << "Already simplified ? " << this << " ";
                                mc.display(tout,this);
                                tout << std::endl;);
    }
    else {
        TRACE("def_simplify", tout << "Simplify " << this << "\n";);
    }
    SASSERT(!m_has_simplified);
    m_has_simplified = true;
    TRACE("def_simplify", tout << "Simplifying ";
                          mc.display(tout,this);
                          tout << "..." << "\n";);
    unsigned i = 0;
    while( i<m_conds.size() ){
        bool found_generalization = false;
        bool can_simplify = true;
        for( unsigned j=(i+1); j<m_conds.size(); j++ ){
            if (mc.is_compatible(m_conds[j], m_conds[i])) {
                if (!mc.is_eq(m_values[j], m_values[i])) {
                    TRACE("def_simplify", mc.display(tout, m_conds[j]); tout << "\n"; tout << j << " is compat, not eq " << i << "\n";);
                    can_simplify = false;
                    break;
                }
                if (mc.is_generalization(m_conds[j], m_conds[i])) {
                    TRACE("def_simplify", tout << j << " is generalized, eq " << i << std::endl;);
                    found_generalization = true;
                    break;
                }
            }
        }
        if( can_simplify && found_generalization ){
            TRACE("def_simplify", tout << "condition ";
                                  mc.display(tout, m_conds[i]);
                                  tout << " is m_inactive." << "\n";);
            m_conds.erase(m_conds.begin()+i);
            m_values.erase(m_values.begin()+i);
        }
        else {
            i++;
        }
    }
}



full_model_check::full_model_check(ast_manager & _m) : m_m(_m), m_au(_m), m_bvu(_m) {
    m_simplification = false;
}


lbool full_model_check::run(mc_context & mc, model_constructor * mct, quantifier * q, expr_ref_buffer & instantiations, expr_ref_buffer & instantiations_star, bool mk_inst_star) {
    TRACE("model_check",tout << "Model check " << mk_pp(q,m_m) << "\n";);

    //classify the body of the quantifier
    classify_info ci(m_m, m_au, m_bvu, q);
    ci.compute();
    TRACE("model_check_classify",tout << "During model check, "; ci.display(tout););
    
    def * d = 0;
    def * db = 0;

    if (ci.has_model_checkable()) {
        expr_ref e(m_m);
        ci.get_model_checkable(e);
        TRACE("mc_operation", tout << "Compute definition...\n";);
        ptr_vector<def> empty_subst;
        d = do_check(mc, mct, q, e, empty_subst);
        TRACE("mc_operation", tout << "Done.\n";);
        TRACE("model_check",tout << "Interpretation of " << mk_pp(e,m_m) << " is : " << "\n";
                            mc.display(tout, d);
                            tout << "\n";);
    }

    bool full_model_check = false;
    /*
    if (full_model_check && !ci.is_model_checkable()) {
        expr_ref eb(m_m);
        ci.get_non_model_checkable(eb);
        TRACE("mc_operation", tout << "Compute definition for bad...\n";);
        ptr_vector<def> approx;
        for (unsigned i=0; i<q->get_num_decls(); i++) {
            def * dx = mc.new_def();
            projection * p = mct->get_projection(mc, q, i);
            value_tuple * def_vt;
            for (unsigned j=0; j<p->get_num_relevant_domain(); j++) {
                val * rv = p->get_relevant_domain_val(j);
                ptr_buffer<abs_val> avals;
                for (unsigned k=0; k<q->get_num_decls(); k++) {
                    avals.push_back(k==i ? mc.mk_value(rv) : p->get_projected_default(mc));
                }
                cond * c = mc.mk_cond(avals);
                value_tuple * rvt = mc.mk_value_tuple(rv);
                dx->append_entry(mc, c, rvt);
                if (j==0) {
                    def_vt = rvt;
                }
            }
            //if (p->get_num_relevant_domain()==0) {
            //    def_vt = mk_value_tuple(mk_val(get_some_value(q->get_decl_sort((q->get_num_decls()-1)-i))));
            //}
            //dx->append_entry(mc, mk_star(mct, q), def_vt);
            TRACE("model_check_bad_debug",tout << "Projection for variable #" << i << " : \n";
                                            mc.display(tout, dx);
                                            tout << "\n";);
            approx.push_back(dx);
        }

        db = do_check(mc, mct, q, eb, approx);
        TRACE("mc_operation", tout << "Done.\n";);
        TRACE("model_check_bad",tout << "Interpretation of (bad part) " << mk_pp(eb,m_m) << " is : " << "\n";
                                mc.display(tout, db);
                                tout << "\n";);
        if (d) {
            def * dc = mc.mk_product(d,db);
            ptr_vector<value_tuple> valts;
            value_tuple * vttrue = mc.mk_value_tuple(mc.mk_val(mc.m_true));
            value_tuple * vtfalse = mc.mk_value_tuple(mc.mk_val(mc.m_false));
            TRACE("model_check_bad",tout << "Combination is : " << "\n";
                                    mc.display(tout, dc);
                                    tout << "\n";);
            
            for (unsigned i=0; i<dc->get_num_entries(); i++) {
                bool is_true = false;
                for (unsigned j=0; j<2; j++) {
                    if (m_m.is_true(to_expr(dc->get_value(i)->get_value(j))->get_value())) {
                        is_true = true;
                        break;
                    }
                }
                valts.push_back(is_true ? vttrue : vtfalse);
            }
            dc->m_values.reset();
            dc->m_values.append(valts.size(), valts.c_ptr());
            d = dc;
        }
        else {
            d = db;
        }
    }
    */

    if (d) {
        TRACE("mc_operation", tout << "Get the instantiations...\n";);
        sbuffer<unsigned> process_star;
        for (unsigned r=0; r<2; r++) {
            //process the entries (add instantiations)
            for (unsigned i=0; i<d->get_num_entries(); i++) {
                //check for false, report exceptions in terms of witnesses
                bool process  = false;
                if (r==0) {
                    value_tuple * vt = d->get_value(i);
                    SASSERT(vt->get_size()==1);
                    val * v = vt->get_value(0);
                    SASSERT(v->is_expr());
                    expr * ve = to_expr(v)->get_value();
                    if (m_m.is_false(ve)) {
                        if (!d->get_condition(i)->is_value()) {
                            process_star.push_back(i);
                        }
                        else {
                            process = true;
                        }
                    }
                }
                else {
                    process = process_star.contains(i);
                }
                if (process) {
                    TRACE("model_check", tout << "Add instantiation for false entry "; mc.display(tout, d->get_condition(i), d->get_value(i)); tout << "\n";);
                    if (r==0) {
                        mc.add_instantiation(mct, q, d->get_condition(i), instantiations, !full_model_check && !ci.is_model_checkable());
                    }
                    else {
                        mc.add_instantiation(mct, q, d->get_condition(i), instantiations_star, !full_model_check && !ci.is_model_checkable());
                    }
                }
            }
            if (!instantiations.empty() || !mk_inst_star) {
                break;
            }
        }
        TRACE("mc_operation", tout << "Done.\n";);
    }

    if (instantiations.empty() && instantiations_star.empty()) {
        return ci.is_model_checkable() ? l_true : l_undef;
    }
    else {
        return l_false;
    }
}

def * full_model_check::do_check(mc_context & mc, model_constructor * mct, quantifier * q, expr * e, ptr_vector<def> & subst) {
    TRACE("model_check_debug",tout << "Model check " << mk_pp(e, m_m) << "...\n";);
    def * d = 0;
    if (is_var(e) || mc.is_atomic_value(e)) {
        if (is_var(e)) {
            //consult an alternate definition, if provided
            unsigned vid = to_var(e)->get_idx();
            if (vid<subst.size()) {
                return subst[vid];
            }
        }
        //trivial case
        d = mc.new_def();
        cond * star = mc.mk_star(mct, q);
        val * v = mc.mk_val(e);
        value_tuple * vt = mc.mk_value_tuple(v);
        d->append_entry(mc, star, vt);
    }
    /*
    else if (is_ground(e)) {

    }
    */
    else if (is_app(e)) {
        //if it is interpreted, we may need to construct definition in a special way
        if (!is_uninterp(e)) {
            var * v;
            expr_ref t(m_m);
            bool is_flipped;
            //first check if it is an relation with a variable
            if ((mct->m_monotonic_projections || m_m.is_eq(e)) && mc.get_classify_util()->is_var_relation(e, v, t, is_flipped)) {
                unsigned vid = v->get_idx();
                if (v->get_idx()>=subst.size()) {
                    TRACE("model_check_debug", tout << "Evaluate as variable relation " << mk_pp(v, m_m) << " ~ " << mk_pp(t, m_m ) << "\n";);
                    //first, model check the term
                    d = do_check(mc, mct, q, t, subst);
                    //then, apply the variable relation on d
                    d = mc.mk_var_relation(d, to_app(e)->get_decl(), v, is_flipped);
                }
            }
            else if (mc.get_classify_util()->is_var_offset(e, v, t, is_flipped, classify_util::REQ_NON_VARIABLE)) {
                if (v->get_idx()>=subst.size()) {
                    TRACE("model_check_debug", tout << "Evaluate as variable offset " << mk_pp(v, m_m) << " + " << mk_pp(t, m_m ) << "\n";);
                    if (t) {
                        //first model check the offset if it exists
                        d = do_check(mc, mct, q, t, subst);
                        //then, apply the variable offset on d
                        d = mc.mk_var_offset(d, v, is_flipped);
                    }
                    else { //make it directly
                        //it should be negated (since e is not the variable itself)
                        SASSERT(is_flipped);
                        d = mc.new_def();
                        cond * cstar = mc.mk_star(mct, q);
                        val * vl = mc.mk_val(v, 0, is_flipped);
                        d->append_entry(mc, cstar, mc.mk_value_tuple(vl));
                    }
                }
            }
        }
        if (!d) {
            //otherwise, will compute product of arguments
            for (unsigned i=0; i<to_app(e)->get_num_args(); i++) {
                expr * ec = to_app(e)->get_arg(i);
                SASSERT(is_uninterp(e) || !is_var(ec) || to_var(ec)->get_idx()<subst.size());
                def * dc = do_check(mc, mct, q, ec, subst);
                if (m_simplification) {
                    dc->simplify(mc);
                }
                d = d ? mc.mk_product(d,dc) : dc;
            }
            TRACE("model_check_debug",if (d) {
                                        tout << "Arguments of " << mk_pp(e,m_m) << " are : " << "\n";
                                        mc.display(tout,d);
                                        tout << "\n";
                                        });
            func_decl * f = to_app(e)->get_decl();
            if (is_uninterp(e)) {
                //uninterpreted case
                def * df = mct->get_def(mc, f);
                if (f->get_arity()==0) {
                    //if constant, look up the definition
                    d = mc.new_def();
                    cond * star = mc.mk_star(mct, q);
                    value_tuple * vt = df->get_value(0);
                    d->append_entry(mc, star, vt);
                } else {
                    TRACE("model_check_debug",tout << "Do uninterpreted compose...\n";);
                    //interpretation is the composition of f with arguments
                    d = mc.mk_compose(df,d);
                    TRACE("model_check_debug",tout << "Done with uninterpreted compose.\n";);
                }
            }
            else {
                TRACE("evaluate_debug", tout << "evaluate for " << mk_pp(e,m_m) << "\n";);
                if (!mc.do_compose(f, d)) {
                    return 0;
                }
            }
        }
    }
    else {
        SASSERT(false);
    }
    TRACE("model_check_debug",tout << "Interpretation of " << mk_pp(e,m_m) << " is : " << "\n";
                                mc.display(tout, d);
                                tout << "\n";);
    SASSERT(d->get_num_entries()>0);
    return d;
}
