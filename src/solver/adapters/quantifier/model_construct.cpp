/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    model_construct.cpp

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-04-02.

--*/

#include"model_construct.h"
#include"ast_pp.h"

#define MODEL_CONSTRUCT_DEBUG

using namespace qsolver;

struct sort_val_indices {
    sort_val_indices(mc_context & mc) : m_mc(mc) {}
    mc_context & m_mc;
    ptr_vector<val> m_args;
    bool operator() (unsigned i, unsigned j) { 
        return m_mc.is_lt(m_args[i],m_args[j]);
    }
};

struct sort_unsigned_indices {
    sbuffer<unsigned> m_args;
    bool operator() (unsigned i, unsigned j) { 
        return m_args[i]<m_args[j];
    }
};

struct sort_pointwise_entry_indices {
protected:
    // 0 means i==j, -1 means i < j, 1 means j < i
    static int compare(mc_context & mc, cond * i, cond * j, ptr_vector<projection> & proj, unsigned index) {
        if (index<proj.size()) {
            if (proj[index]->get_projection_type()!=projection::PROJ_POINTWISE || j->get_value(index)==i->get_value(index)) {
                return compare(mc, i, j, proj, index+1);
            }
            else {
                abs_val * pvj = proj[index]->get_projected_value(mc, to_value(j->get_value(index))->get_value());
                abs_val * pvi = proj[index]->get_projected_value(mc, to_value(i->get_value(index))->get_value());
                if (pvj->is_star()) {
                    return -1;
                }
                else if (pvi->is_star()) {
                    return 1;
                }
                else {
                    int cmp = compare(mc, i, j, proj, index+1);
                    return cmp==0 ? (i->get_value(index)<j->get_value(index) ? -1 : 1) : cmp;
                }
            }
        }
        else {
            return 0;
        }
    }
public:
    //compare two conditions wrt to pointwise entries
    static int compare(mc_context & mc, cond * i, cond * j, ptr_vector<projection> & proj) { 
        SASSERT(i->get_size()==j->get_size());
        SASSERT(i->get_size()==proj.size());
        return compare(mc, i, j, proj, 0); 
    }
public:
    sort_pointwise_entry_indices(mc_context & mc, ptr_vector<projection> & proj, def * d) : m_mc(mc), m_proj(proj), m_def(d) {}
    mc_context & m_mc;
    ptr_vector<projection> & m_proj;
    def * m_def;
    bool operator() (unsigned i, unsigned j) {
        return compare(m_mc, m_def->get_condition(i), m_def->get_condition(j), m_proj)==-1;
    }
};




projection::projection()  {
    reset();
}

void projection::reset() {
    m_find = 0;
    m_type = PROJ_POINTWISE;
    m_rel_domain_pre.reset();
    m_rel_domain.reset();
    m_rel_domain_val.reset();
    m_rel_domain_val_ind.reset();
    m_projection_term = 0;
    m_no_projection_terms.reset();
    m_projection_term_val = 0;
    m_monotonic_intervals.reset();
    m_offset = 0;
    m_offset_valid = true;
    m_proj_def = 0;
}

void projection::merge(projection * p) {
    if (p!=this) {
        SASSERT(!m_find);
        SASSERT(!p->m_find);
        SASSERT(!m_offset);
        SASSERT(!p->m_offset);
        m_find = p;
        //carry the information
        if (m_type==PROJ_MONOTONIC) {
            p->m_type = m_type;
        }
        for (unsigned i=0; i<m_rel_domain_pre.size(); i++) {
            p->add_relevant_domain(m_rel_domain_pre[i]);
        }
        m_rel_domain_pre.reset();
        for (unsigned i=0; i<m_no_projection_terms.size(); i++) {
            p->add_no_projection_term(m_no_projection_terms[i]);
        }
        m_no_projection_terms.reset();
        //TODO: carry more information?
    }
}

bool projection::merge_with_offset(projection * p, expr * o) {
    projection * r = get_rep();
    projection * pr = p->get_rep();
    if (o) {
        if (!m_offset && !p->m_offset) {
            r->merge(pr);
            m_offset = o;
            return true;
        }
        else if (m_offset) {
            //TODO!!!
            if (p->m_offset) {
                //both already have offsets
                //check if o+m_offset = p->m_offset
            }
            else {
                //only this has offset
            }
        }
        else{
            //only other has offset

        }
        m_offset_valid = false;
        return false;
    }else{
        r->merge(pr);
        return true;
    }
}

projection * projection::get_rep() {
    if (!m_find) {
        return this;
    }
    else {
        projection * p = m_find->get_rep();
        m_find = p;
        //carry offset when condensing
        return p;
    }
}

void projection::set_projection_term(expr * e) { 
    SASSERT(!m_no_projection_terms.contains(e));
    m_projection_term = e; 
}

void projection::add_no_projection_term(expr * e) {
    if (!m_no_projection_terms.contains(e)) {
        m_no_projection_terms.push_back(e);
    }
}

void projection::add_relevant_domain(expr * e) {
    if (!m_rel_domain_pre.contains(e)) {
        m_rel_domain_pre.push_back(e);
    }
}

void projection::add_relevant_domain(expr * e, val * v) {
    if (!m_rel_domain_val.contains(v)) {
        SASSERT(m_rel_domain.size()==m_rel_domain_val.size());
        m_rel_domain.push_back(e);
        m_rel_domain_val_ind.insert(v,m_rel_domain_val.size());
        m_rel_domain_val.push_back(v);
    }
}

void projection::assert_partial_model(mc_context & mc, obj_map< expr, expr * > & m, sort * s) {
    TRACE("model_construct_debug",tout << "Compute values of terms in the relevant domain...\n";
                                  if (!m_rel_domain_pre.empty()) {
                                      tout << "Expressions are : \n";
                                      for (unsigned i=0; i<m_rel_domain_pre.size(); i++) {
                                          tout << "   ";
                                          mc.display(tout, m_rel_domain_pre[i]);
                                          tout << "\n";
                                      }
                                  });
    //reconstruct the relevant domain based on the terms in the relevant domain
    for (unsigned i=0; i<m_rel_domain_pre.size(); i++) {
        expr * ecv = m_rel_domain_pre[i];
        //must evaluate if it is not atomic
        if (!mc.is_atomic_value(m_rel_domain_pre[i])) {
            if (!m.contains(m_rel_domain_pre[i])) {
                std::cout << "WARN #3" << std::endl;
                TRACE("model_construct_warn", tout << "WARNING : this term needs to be in partial model : ";
                                              mc.display(tout, m_rel_domain_pre[i]);
                                              tout << std::endl;);
            }
            SASSERT(m.contains(m_rel_domain_pre[i]));
            ecv = m.find(m_rel_domain_pre[i]);
        }
        val * ecvv = mc.mk_val(ecv);
        TRACE("model_construct_debug", tout << "Adding for term "; mc.display(tout,m_rel_domain_pre[i]); 
                                       tout << ", value is "; mc.display(tout,ecvv); tout << "\n";);
        add_relevant_domain(m_rel_domain_pre[i], ecvv);
    }
    //if we have a projection term, get its value
    if (m_type==PROJ_POINTWISE) {
        TRACE("model_construct_debug", tout << "Select a projection term...\n";
                                       if (!m_no_projection_terms.empty()) {
                                           tout << "These terms are ineligible: \n";
                                           for (unsigned i=0; i<m_no_projection_terms.size(); i++) {
                                               tout << "  ";
                                               mc.display(tout, m_no_projection_terms[i]);
                                               tout << "\n";
                                           }
                                       });
        ptr_vector<val> no_vals;
        for (unsigned i=0; i<m_no_projection_terms.size(); i++) {
            expr * ecnpt = m_no_projection_terms[i];
            if (!mc.is_atomic_value(m_no_projection_terms[i])) {
                TRACE("model_construct_warn", tout << "WARNING : this term needs to be in partial model : ";
                                              mc.display(tout, m_no_projection_terms[i]);
                                              tout << "\n";);
                SASSERT(m.contains(m_no_projection_terms[i]));
                ecnpt = m.find(m_no_projection_terms[i]);
            }
            val * npv = mc.mk_val(ecnpt);
            no_vals.push_back(npv);
        }
        //look for an appropriate projection term
        unsigned next_index = 0;
        bool tried_mk_dist_const = false;  //TODO: use type enumerator
        do {
            bool success = false;
            if (m_projection_term) {
                success = true;
                expr * ecpt = m_projection_term;
                if (!mc.is_atomic_value(ecpt)) {
                    if (m.contains(ecpt)) {
                        ecpt = m.find(ecpt);
                    }
                    else {
                        //make whatever value you want (it does not matter) 
                        ecpt = mc.get_some_value(s);
                    }
                }
                m_projection_term_val = mc.mk_val(ecpt);

                //make sure it is different from all the no_projection_terms
                for (unsigned i=0; i<no_vals.size(); i++) {
                    if (mc.is_eq(m_projection_term_val, no_vals[i])) {
                        success = false;
                        break;
                    }
                }
            }
            if (!success) {
                //try the next term in the relevant domain as projection term
                m_projection_term_val = 0;
                if (next_index<m_rel_domain.size()) {
                    m_projection_term = m_rel_domain[next_index];
                    next_index++;
                }
                else {
                    //if we still don't have a projection term, then make any (this will be the case if none is provided and the relevant domain is empty)
                    m_projection_term = tried_mk_dist_const ? 0 : mc.mk_distinguished_constant_expr(s);
                    tried_mk_dist_const = true;
                }
            }
        }
        while (!m_projection_term_val && m_projection_term);
        SASSERT(m_projection_term);
        SASSERT(m_projection_term_val);
    }
    TRACE("model_construct_debug",tout << "Finished preparing projection.\n";);
}

void projection::compute(mc_context & mc) {
    if (m_type==projection::PROJ_POINTWISE) {
        //nothing to do
    }
    else if (m_type==projection::PROJ_MONOTONIC) {
        //if not done so already, compute the intervals
        if (m_monotonic_intervals.size()<m_rel_domain_val.size()) {
            compute_intervals(mc, m_rel_domain_val, m_monotonic_intervals);

            //put the last interval last, if necessary
            for (unsigned i=0; i<(m_monotonic_intervals.size()-1); i++) {
                if (!m_monotonic_intervals[i]->get_upper()) {
                    //swap the indicies
                    m_rel_domain_val_ind.erase(m_rel_domain_val[i]);
                    m_rel_domain_val_ind.insert(m_rel_domain_val[i], m_rel_domain_val.size()-1);
                    m_rel_domain_val_ind.erase(m_rel_domain_val[m_rel_domain_val.size()-1]);
                    m_rel_domain_val_ind.insert(m_rel_domain_val[m_rel_domain_val.size()-1], i);
                    //swap the values in the maps
                    expr * tmpe = m_rel_domain[i];
                    val * tmpv = m_rel_domain_val[i];
                    av_interval * tmpav = m_monotonic_intervals[i];
                    m_rel_domain[i] = m_rel_domain[m_rel_domain.size()-1];
                    m_rel_domain_val[i] = m_rel_domain_val[m_rel_domain_val.size()-1];
                    m_monotonic_intervals[i] = m_monotonic_intervals[m_monotonic_intervals.size()-1];
                    m_rel_domain[m_rel_domain.size()-1] = tmpe;
                    m_rel_domain_val[m_rel_domain_val.size()-1] = tmpv;
                    m_monotonic_intervals[m_monotonic_intervals.size()-1] = tmpav;
                    break;
                }
            }

        }
    }
}

abs_val * projection::get_projected_value(mc_context & mc, val * v) {
    //first compute the necessary information
    compute(mc);
    if (m_type==projection::PROJ_POINTWISE) {
        SASSERT(m_projection_term_val);
        if (mc.is_eq(v, m_projection_term_val)) {
            return mc.mk_star();
        }
        else {
            return mc.mk_value(v);
        }
    }
    else if (m_type==projection::PROJ_MONOTONIC) {
        SASSERT(m_rel_domain_val_ind.contains(v));
        unsigned vi = m_rel_domain_val_ind.find(v);
        return m_monotonic_intervals[vi];
    }
    else {
        SASSERT(false);
        return mc.mk_value(v);
    }
}

abs_val * projection::get_projected_default(mc_context & mc) {
    //first compute the necessary information
    compute(mc);
    if (m_type==projection::PROJ_POINTWISE) {
        return mc.mk_star();
    }
    else if (m_type==projection::PROJ_MONOTONIC) {
        //return mc.mk_star();
        return mc.mk_interval(0, 0);
    }
    else {
        SASSERT(false);
        return mc.mk_star();
    }
}

void projection::get_witness(mc_context & mc, abs_val * a, expr_ref & e, expr * o, bool & found_expr) {
    found_expr = false;
    TRACE("inst_debug",tout << "Getting witness for ";
                       mc.display(tout, a);
                       if (o) {
                           tout << " with offset ";
                           mc.display(tout, o);
                       }
                       tout << "\n";
                       if (m_type==projection::PROJ_POINTWISE){
                           tout << "Projection term is : ";
                           if (m_projection_term) {
                               mc.display(tout,m_projection_term);
                           } 
                           else {
                               tout << "[NULL]"; 
                           }
                           tout << "\n";
                       }
                       tout << "Relevant domain is : ";
                       for (unsigned i=0; i<m_rel_domain.size(); i++) {
                           tout << "  ";
                           mc.display(tout, m_rel_domain[i]);
                           tout << " -> ";
                           mc.display(tout, m_rel_domain_val[i]);
                           tout << "\n";
                       });
    compute(mc);
    val * v = 0;
    if (a->is_value()) {
        v = to_value(a)->get_value();
    }
    else if (a->is_star()) {
        SASSERT(m_type==projection::PROJ_POINTWISE);
        SASSERT(m_projection_term);
        e = m_projection_term;
        found_expr = true;
    }
    else if (a->is_interval()) {
        SASSERT(m_type==projection::PROJ_MONOTONIC);
        v = to_interval(a)->get_upper();
        if (!v) {
            SASSERT(!m_monotonic_intervals.empty());
            v = m_rel_domain_val[m_monotonic_intervals.size()-1];
            //interval should contain the highest value in the relevant domain
            SASSERT(!mc.is_lt(v, to_interval(a)->get_lower()));
        }
    } 
    else {
        SASSERT(false);
    }
    //get the expression
    if (!e) {
        //add offset value
        v = o ? mc.mk_offset(v, mc.mk_val(o)) : v;
        //make sure it contains the value
        if (m_rel_domain_val_ind.contains(v)) {
            unsigned i = m_rel_domain_val_ind.find(v);
            e = m_rel_domain[i];
            found_expr = true;
        }
        else {
            //just make an expression from the value
            mc.get_expr_from_val(v, e);
        }
    }
    if (o) {
        mc.mk_offset_sub(e, o, e);
    }
    TRACE("inst_debug",tout << "returning "; mc.display(tout,e); tout << "\n";);
}


def * projection::get_definition(mc_context & mc) {
    if (!m_proj_def) {
        m_proj_def = mc.new_def();
        if (m_type==projection::PROJ_POINTWISE) {
            //it is all values in relevant domain v->v, followed by *->eval(e)
            for (unsigned i=0; i<m_rel_domain_val.size(); i++) {
                ptr_buffer<abs_val> avals;
                avals.push_back(mc.mk_value(m_rel_domain_val[i]));
                cond * c = mc.mk_cond(avals);
                value_tuple * vt = mc.mk_value_tuple(m_rel_domain_val[i]);
                m_proj_def->append_entry(mc, c, vt);
            }
            cond * c = mc.mk_star(1);
            value_tuple * vt = mc.mk_value_tuple(m_projection_term_val);
            m_proj_def->append_entry(mc, c, vt);
        }
        else if (m_type==projection::PROJ_MONOTONIC) {
            //it is the set of intervals
            for (unsigned i=0; i<m_rel_domain_val.size(); i++) {
                ptr_buffer<abs_val> avals;
                avals.push_back(m_monotonic_intervals[i]);
                cond * c = mc.mk_cond(avals);
                value_tuple * vt = mc.mk_value_tuple(m_rel_domain_val[i]);
                m_proj_def->append_entry(mc, c, vt);
            }
        }
        m_proj_def->simplify(mc);
    }
    return m_proj_def;
}

void projection::compute_intervals(mc_context & mc, ptr_vector<val> & vals, ptr_vector<av_interval> & intervals) {
    sort_val_indices svi(mc);
    sbuffer<unsigned> indices;
    SASSERT(!vals.empty());
    bool is_int = vals[0]->is_int();
    bool is_bv = vals[0]->is_bv();
    for (unsigned j=0; j<vals.size(); j++) {
        SASSERT(!is_int || vals[j]->is_int());
        SASSERT(!is_bv || vals[j]->is_bv());
        svi.m_args.push_back(vals[j]);
        indices.push_back(j);
    }
    //do the sort
    std::sort(indices.begin(), indices.end(), svi);
    //construct the correspond intervals
    ptr_vector<av_interval> intervals_ordered;
    val * curr_lower = 0;
    av_interval * curr_interval = 0;
    sbuffer<unsigned> indices_to_orig;
    indices_to_orig.resize(indices.size());
    for (unsigned i=0; i<indices.size(); i++) {
        val * curr_upper = (i==indices.size()-1) ? 0 : svi.m_args[indices[i]];
        curr_interval = mc.mk_next_interval(curr_lower,curr_upper);
        intervals_ordered.push_back(curr_interval);
        curr_lower = curr_upper;
        indices_to_orig[indices[i]] = i;
    }
    for (unsigned i=0; i<indices_to_orig.size(); i++) {
        intervals.push_back(intervals_ordered[indices_to_orig[i]]);
    }
    TRACE("proj_monotonic", tout << "values are : \n";
                            for (unsigned j=0; j<vals.size(); j++) {
                                tout << "  ";
                                mc.display(tout,vals[j]);
                                tout << "\n";
                            }
                            tout << "Corresponding intervals are: \n";
                            for (unsigned j=0; j<intervals.size(); j++) {
                                tout << "  ";
                                mc.display(tout,intervals[j]);
                                tout << "\n";
                            });
}

model_constructor::model_constructor(ast_manager & _m)
    : m_m(_m), m_au(_m), m_bvu(_m), m_partial_model_terms(_m) {
    m_use_projection_definitions = false;
}

void model_constructor::reset_round(mc_context & mc) {
    for (unsigned i=0; i<m_funcs.size(); i++) {
        ptr_vector<projection> & proj = m_func_arg_proj.find(i);
        for (unsigned j=0; j<proj.size(); j++) {
            proj[j]->reset();
        }
    }

    for (unsigned i=0; i<m_quants.size(); i++) {
        ptr_vector<projection> & proj = m_quant_var_proj.find(i);
        for (unsigned j=0; j<proj.size(); j++) {
            proj[j]->reset();
        }
    }
    m_ground_def.reset();
    m_def.reset();
    m_partial_model_terms.reset();
}

void model_constructor::process(mc_context & mc, expr * e, ptr_vector<projection> & var_proj, bool hasPolarity, bool polarity) {
    if (is_app(e) && !is_ground(e)) {
        bool newHasPolarity = hasPolarity && !m_m.is_iff(e);    //ITE handled below
        bool newPolarity = m_m.is_not(e) ? !polarity : polarity;
        //process the children
        for (unsigned i=0; i<to_app(e)->get_num_args(); i++) {
            expr * ec = to_app(e)->get_arg(i);
            if (is_uninterp(e)) {
                if (is_var(ec)) {
                    unsigned vid = to_var(ec)->get_idx();
                    projection * vp = var_proj[vid]->get_rep(); 
                    projection * fp = get_projection(mc, to_app(e)->get_decl(), i);
                    //merge projection if uninterpreted
                    vp->merge(fp);
                }
                else if (is_ground(ec)) {
                    projection * fp = get_projection(mc, to_app(e)->get_decl(), i);
                    add_relevant_domain(fp, ec);
                }
                else {
                    var * v;
                    expr_ref offset(m_m);
                    bool is_negated;
                    if (mc.get_classify_util()->is_var_offset(ec, v, offset, is_negated, classify_util::REQ_GROUND)) {
                        unsigned vid = v->get_idx();
                        projection * vp = var_proj[vid]; 
                        projection * fp = get_projection(mc, to_app(e)->get_decl(), i, false);
                        if (offset && m_au.is_zero(offset)) {
                            offset = 0;
                        }
                        vp->merge_with_offset(fp, offset);
                        if (!m_partial_model_terms.contains(offset)) {
                            m_partial_model_terms.push_back(offset);
                        }
                    }
                }
            }
            bool newHasPolarity2 = newHasPolarity && (!m_m.is_ite(e) || i!=0);
            process(mc, ec, var_proj, newHasPolarity2, newPolarity);
        }
        if (!is_uninterp(e)) {
            var * v1 = 0;
            var * v2 = 0;
            ptr_vector<expr> no_proj_terms;
            expr_ref_buffer rel_domain(m_m); 
            unsigned proj_type = projection::PROJ_POINTWISE;
            if (mc.get_classify_util()->is_witnessable(e, hasPolarity, polarity, v1, v2, no_proj_terms, rel_domain, proj_type, false)) {
                TRACE("rel_domain_debug", tout << "Processing variable relation for relevant domain : " << mk_pp(e,m_m) << " ";
                                          if (hasPolarity) tout << "(polarity = " << hasPolarity << ")\n";);
                unsigned vid = v1->get_idx();
                projection * vp = var_proj[vid]->get_rep(); 
                //add no projection terms
                for (unsigned r=0; r<no_proj_terms.size(); r++) {
                    TRACE("rel_domain_debug", tout << "Term " << mk_pp(no_proj_terms[r],m_m) << " should not be chosen as projection term.\n";);
                    vp->add_no_projection_term(no_proj_terms[r]);
                    if (!m_partial_model_terms.contains(no_proj_terms[r])) {
                        m_partial_model_terms.push_back(no_proj_terms[r]);
                    }
                }
                //add relevant domain
                for (unsigned r=0; r<rel_domain.size(); r++) {
                    TRACE("rel_domain_debug", tout << "Term " << mk_pp(rel_domain[r],m_m) << " is in the relevant domain.\n";);
                    add_relevant_domain(vp, rel_domain[r]);
                }
                //set projection to monotonic if necessary
                if (proj_type==projection::PROJ_MONOTONIC) {
                    TRACE("rel_domain_debug", tout << "Projection of " << mk_pp(v1,m_m) << " should be monotonic.\n";);
                    vp->set_projection_type(proj_type);
                }
                //if there is a second varible, merge their projections
                if (v2) {
                    TRACE("rel_domain_debug", tout << "Projections of " << mk_pp(v1,m_m) << " and " << mk_pp(v2,m_m) << " should be equal.\n";);
                    unsigned vid2 = v2->get_idx();
                    //TODO: the offsets need to be managed properly
                    projection * vp2 = var_proj[vid2]->get_rep(); 
                    vp->merge(vp2);
                }
            }
        }
    }
}

void model_constructor::assert_quantifier(mc_context & mc, quantifier * q) {
    TRACE("rel_domain", tout << "Process relevant domain information for quantified formula " << mk_pp(q,m_m) << "\n";);
    unsigned qid = get_quantifier_id(mc, q);
    process(mc, q->get_expr(), m_quant_var_proj.find(qid), true, true);
}

void model_constructor::set_projection_term(mc_context & mc, expr * t) {
    SASSERT(is_app(t));
    SASSERT(is_uninterp(t));
    func_decl * f = to_app(t)->get_decl();
    for (unsigned i=0; i<f->get_arity(); i++) {
        expr * tc = to_app(t)->get_arg(i);
        set_projection_term(mc, f, i, tc);
    }
}

void model_constructor::set_projection_term(mc_context & mc, func_decl * f, unsigned i, expr * e) {
    TRACE("model_construct_debug", tout << "Set projection term ";
                                   mc.display(tout, e);
                                   tout << " for " << mk_pp(f,m_m) << ", arugment " << i << "\n";);
    projection * p = get_projection(mc, f, i);
    p->set_projection_term(e);
    if (!m_partial_model_terms.contains(e)) {
        m_partial_model_terms.push_back(e);
    }
}

void model_constructor::assert_partial_model(mc_context & mc, obj_map< expr, expr * > & m) {
    TRACE("model_construct",tout << "Asserting ground model assignments..." << "\n";);
    //process ground constraints
    for (obj_map< expr, expr * >::iterator it = m.begin(); it != m.end(); ++it) {
        expr * e = it->m_key;
        expr * ev = it->m_value;
        if (is_uninterp(e)) {
            func_decl * f = to_app(e)->get_decl();
            TRACE("model_construct_debug",tout << "Assert ";
                                          mc.display(tout, e);
                                          tout << " -> ";
                                          mc.display(tout,ev);
                                          tout << "\n";);
            ptr_buffer<abs_val> avals;
            for (unsigned i = 0; i<to_app(e)->get_num_args(); i++ ){
                expr * ec = to_app(e)->get_arg(i);
                expr * ecv = ec;
                //must evaluate if it is not atomic
                if (!mc.is_atomic_value(ec)) {
                    SASSERT(m.contains(ec));
                    ecv = m.find(ec);
                }
                val * v = mc.mk_val(ecv);
                avals.push_back(mc.mk_value(v));
                //record witness for relevant domain
                projection * p = get_projection(mc, f, i);
                p->add_relevant_domain(ec, v);
            }
            cond * c = mc.mk_cond(avals);
            def * ed = get_ground_def(mc, f);
            value_tuple * vt = mc.mk_value_tuple(mc.mk_val(ev));
            ed->append_entry(mc, c, vt);
        }
        //add to universe if range is uninterpreted sort
        sort * sev = get_sort(ev);
        if (m_m.is_uninterp(sev)) {
            if (!m_universe.contains(sev)) {
                m_universe.insert(sev, ptr_vector<expr>());
            }
            ptr_vector<expr> & univ = m_universe.find(sev);
            if (!univ.contains(ev)) {
                univ.push_back(ev);
            }
        }
    }
    TRACE("model_construct",tout << "Computing relevant domain values..." << "\n";);
    //fill in values for relevant domains
    ptr_vector<projection> processed;
    //compute the relevant domain values
    for (unsigned i=0; i<m_funcs.size(); i++) {
        func_decl * f = m_funcs[i];
        SASSERT(m_func_to_id.contains(f));
        SASSERT(m_func_to_id.find(f)==i);
        SASSERT(is_uninterp(f));
        for (unsigned j=0; j<f->get_arity(); j++) {
            projection * p = get_projection(mc, f, j);
            if (!processed.contains(p)) {
                TRACE("model_construct_debug",tout << "Process projection for " << mk_pp(f,m_m) << ", argument " << j << "\n";);
                p->assert_partial_model(mc, m, f->get_domain(j));
                processed.push_back(p);
            }
        }
    }
    for (unsigned i=0; i<m_quants.size(); i++) {
        quantifier * q = m_quants[i];
        SASSERT(m_quant_to_id.contains(q));
        SASSERT(m_quant_to_id.find(q)==i);
        for (unsigned j=0; j<q->get_num_decls(); j++) {
            projection * p = get_projection(mc, q, j);
            if (!processed.contains(p)) {
                TRACE("model_construct_debug",tout << "Process projection for " << mk_pp(q,m_m) << ", variable " << j << "\n";);
                p->assert_partial_model(mc, m, q->get_decl_sort((q->get_num_decls()-1)-j));
                processed.push_back(p);
            }
        }
    }
}

unsigned model_constructor::get_func_id(mc_context & mc, func_decl * f) {
    SASSERT(is_uninterp(f));
    if (!m_func_to_id.contains(f)) {
        m_func_to_id.insert(f, m_funcs.size());
        //make projections for the arguments
        ptr_vector<projection> arg_eqc;
        for (unsigned i=0; i<f->get_arity(); i++) {
            void * mem = mc.allocate(sizeof(projection));
            arg_eqc.push_back(new (mem) projection());
        }
        m_func_arg_proj.insert(m_funcs.size(), arg_eqc);
        m_funcs.push_back(f);
        return m_funcs.size()-1;
    }
    return m_func_to_id.find(f);
}

unsigned model_constructor::get_quantifier_id(mc_context & mc, quantifier * q) {
    if (!m_quant_to_id.contains(q)) {
        m_quant_to_id.insert(q, m_quants.size());
        //make equivalence classes for the arguments
        ptr_vector<projection> arg_eqc;
        for (unsigned i=0; i<q->get_num_decls(); i++) {
            void * mem = mc.allocate(sizeof(projection));
            arg_eqc.push_back(new (mem) projection());
        }
        m_quant_var_proj.insert(m_quants.size(), arg_eqc);
        m_quants.push_back(q);
        return m_quants.size()-1;
    }
    else {
        return m_quant_to_id.find(q);
    }
}

def * model_constructor::get_ground_def(mc_context & mc, func_decl * f) {
    unsigned id = get_func_id(mc, f);
    if (!m_ground_def.contains(id)) {
        def * d = mc.new_def();
        m_ground_def.insert(id, d);
        return d;
    }
    return m_ground_def.find(id);
}

void model_constructor::construct_entries(mc_context & mc, func_decl * f, def * dg, sbuffer<unsigned> & order_indices, 
                                          sbuffer<unsigned> & process_entries, ptr_buffer<abs_val> & avals,
                                          def * d) {
    unsigned index = avals.size();
    if (index==f->get_arity()) {
        //add entry
        for (unsigned i=0; i<process_entries.size(); i++) {
            cond * c = mc.mk_cond(avals);
            value_tuple * vt = dg->get_value(order_indices[process_entries[i]]);
            TRACE("model_construct_debug", tout << "Add entry ";
                                            mc.display(tout, c);
                                            tout << " -> ";
                                            mc.display(tout, vt);
                                            tout << "\n";);
            if (!d->append_entry(mc, c, vt)) {
                std::cout << "WARN #1" << std::endl;
                TRACE("model_construct_warn",
                    tout << mk_pp(f,m_m);
                    tout << " Did not append entry! ";
                    mc.display(tout, c);
                    tout << " -> ";
                    mc.display(tout, vt);
                    tout << std::endl;);
            }
        }
    }
    else {
        projection * p = get_projection(mc, f, index);
        if (p->get_projection_type()==projection::PROJ_POINTWISE) {
            //looking up any condition should work (they are all the same)
            unsigned entry_index = order_indices[process_entries[0]];
            abs_val * a = dg->get_condition(entry_index)->get_value(index);
            avals.push_back(p->get_projected_value(mc, to_value(a)->get_value()));
            construct_entries(mc, f, dg, order_indices, process_entries, avals, d);
            avals.pop_back();
        }
        else if (p->get_projection_type()==projection::PROJ_MONOTONIC) {
            //partion the entries in process_entries into sets with equal values at index
            ptr_vector<val> vals;
            ptr_vector<av_interval> intervals;
            sbuffer< sbuffer<unsigned> > process_entry_children;
            ptr_addr_map<val, unsigned> val_ind; //indices lookup
            //add all unique values
            for (unsigned i=0; i<process_entries.size(); i++) {
                unsigned entry_index = order_indices[process_entries[i]];
                abs_val * a = dg->get_condition(entry_index)->get_value(index);
                val * v = to_value(a)->get_value();
                if (!val_ind.contains(v)) {
                    val_ind.insert(v,vals.size());
                    process_entry_children.push_back(sbuffer<unsigned>());
                    process_entry_children[vals.size()].push_back(process_entries[i]);
                    vals.push_back(v);
                }
                else {
                    unsigned vi = val_ind.find(v);
                    process_entry_children[vi].push_back(process_entries[i]);
                }
            }
            TRACE("model_construct_debug", tout << "At index = " << index << ", we have " << vals.size() << " values for monotonic projection\n";);
            //compute the corresponding intervals
            projection::compute_intervals(mc, vals, intervals);
            //now, recurse
            for (unsigned i=0; i<vals.size(); i++) {
                avals.push_back(intervals[i]);
                construct_entries(mc, f, dg, order_indices, process_entry_children[i], avals, d);
                avals.pop_back();
            }
        }
        else {
            SASSERT(false);
        }
    }
}

void model_constructor::add_relevant_domain(projection * p, expr * e) {
    p->add_relevant_domain(e);
    if (!m_partial_model_terms.contains(e)) {
        m_partial_model_terms.push_back(e);
    }
}

def * model_constructor::get_def(mc_context & mc, func_decl * f) {
    unsigned id = get_func_id(mc, f);
    if (!m_def.contains(id)) {
        //the ground definition
        def * dg = get_ground_def(mc, f);
        //d is the complete definition we will construct
        def * d;
        TRACE("model_construct",tout << "Constructing definition for " << mk_pp(f,m_m) << "... " << "\n";
                                tout << "Ground definition is: \n";
                                mc.display(tout, dg);
                                tout << "\n";);
        if (dg->get_num_entries()==0) {
            //need to make at least one entry
            d = mc.new_def();
            cond * cstar = mc.mk_star(f->get_arity());
            val * v = mc.mk_val(mc.get_some_value(f->get_range()));
            value_tuple * vt = mc.mk_value_tuple(v);
            d->append_entry(mc, cstar, vt);
        }
        else {
            //get projections
            bool has_monotonic = false;
            bool is_complete = true;
            ptr_vector<projection> projs;
            for (unsigned k=0; k<f->get_arity(); k++) {
                projs.push_back(get_projection(mc, f, k));
                if (projs[k]->get_projection_type()==projection::PROJ_MONOTONIC) {
                    has_monotonic = true;
                }
            }
            //now, complete the definition
            if (m_use_projection_definitions) {
                //get the projection for the function
                def * dp = get_projection_definition(mc, f);
                if (dp) {
                    //complete definition is the ground definition composed with projection
                    d = mc.mk_compose(dg, dp);
                }
                else {
                    d = dg;
                    SASSERT(f->get_arity()==0);
                }
            }
            else {
                d = mc.new_def();
                //determine the order to process the entries (so that their projected conditions do not get subsumed)
                sbuffer<unsigned> order_indices;
                if (!has_monotonic) {
                    //easy case: the order is determined by the # of default values in the projection
                    sort_unsigned_indices sui;
                    for( unsigned j=0; j<dg->get_num_entries(); j++ ){
                        unsigned pvCount = 0;
                        for (unsigned k=0; k<f->get_arity(); k++) {
                            if (projs[k]->get_projection_type()==projection::PROJ_POINTWISE) {
                                abs_val * a = dg->get_condition(j)->get_value(k);
                                val * v = to_value(a)->get_value();
                                abs_val * pv = projs[k]->get_projected_value(mc, v);
                                if (pv->is_star()) {
                                    pvCount++;
                                }
                            }
                        }
                        order_indices.push_back(j);
                        sui.m_args.push_back(pvCount);
                    }
                    //do the sort
                    std::sort(order_indices.begin(), order_indices.end(), sui);
                }
                else {
                    sort_pointwise_entry_indices spwi(mc, projs, dg);
                    for( unsigned j=0; j<dg->get_num_entries(); j++ ){
                        order_indices.push_back(j);
                    }
                    //do the sort
                    std::sort(order_indices.begin(), order_indices.end(), spwi);
                    TRACE("model_construct_debug", tout << "Sorted with respect to pointwise entries: \n";
                                                    for (unsigned i=0; i<order_indices.size(); i++) {
                                                        tout << "   ";
                                                        mc.display(tout, dg->get_condition(order_indices[i]));
                                                        tout << " -> ";
                                                        mc.display(tout, dg->get_value(order_indices[i]));
                                                        tout << "\n";
                                                    });
                }

                //complete the function definition
                unsigned entry_index = 0;
                while (entry_index<dg->get_num_entries()) {
                    unsigned entry_start = entry_index;
                    sbuffer<unsigned> process_entries;
                    bool continue_iter = true;
                    while (continue_iter) {
                        process_entries.push_back(entry_index);
                        entry_index++;
                        //if monotonic projection exists, continue iterating while pointwise component of entries are the same
                        continue_iter = (has_monotonic && entry_index<dg->get_num_entries() && 
                                         sort_pointwise_entry_indices::compare(mc, dg->get_condition(order_indices[entry_index]), dg->get_condition(order_indices[entry_start]), projs)==0);
                    }
                    TRACE("model_construct_debug", tout << "Process entries " << entry_start << " .... " << (entry_index-1) << "\n";);
                    //process order_indicies[entry_start]....order_indicies[entry_index-1]
                    ptr_buffer<abs_val> avals;
                    construct_entries(mc, f, dg, order_indices, process_entries, avals, d);
                }
                //check if complete: look at last entry
                cond * c_last = d->get_condition(d->get_num_entries()-1);  
                for (unsigned k=0; k<f->get_arity(); k++) {
                    if (projs[k]->get_projection_type()==projection::PROJ_POINTWISE && !c_last->get_value(k)->is_star()) {
                        is_complete = false;
                        break;
                    }
                }
            }
            //if it is not complete, complete it
            if (!is_complete) {
                ptr_buffer<abs_val> avals;
                for (unsigned k=0; k<f->get_arity(); k++) {
                    abs_val * av = projs[k]->get_projected_default(mc);
                    avals.push_back(av);
                }
                cond * cstar = mc.mk_cond(avals);
                value_tuple * def_val = dg->get_value(0);
                TRACE("model_construct",tout << "Complete the definition with ";
                                        mc.display(tout,cstar);
                                        tout << " -> ";
                                        mc.display(tout,def_val);
                                        tout << "\n";);
                d->append_entry(mc, cstar, def_val);
            }
            //simplify the definition
            d->simplify(mc);
#ifdef MODEL_CONSTRUCT_DEBUG
            //for debugging: make sure all ground arguments agree on their evaluation
            for (unsigned i=0; i<dg->get_num_entries(); i++) {
                value_tuple * vt = d->evaluate(mc, dg->get_condition(i));
                if (!mc.is_eq(vt->get_value(0), dg->get_value(i)->get_value(0))) {
                    std::cout << "WARN #2" << std::endl;
                    TRACE("model_construct_warn",tout << "WARNING: the following ground constraint is not satisfied by model construction: \n";
                                                 tout << "  Function : " << mk_pp(f,m_m) << "\n";
                                                 tout << "  Constraint : ";
                                                 mc.display(tout, dg->get_condition(i));
                                                 tout << " -> ";
                                                 mc.display(tout, dg->get_value(i));
                                                 tout << "\n";
                                                 tout << "  Got result : ";
                                                 mc.display(tout, vt);
                                                 tout << "\n";);
                }
            }
#endif
        }
        //display
        TRACE("model_construct",tout << "Definition for " << mk_pp(f,m_m) << ": " << "\n";
                                mc.display(tout, d);
                                tout << "\n";);

        m_def.insert(id, d);
        return d;
    }
    return m_def.find(id);
}

//get universe size
unsigned model_constructor::get_num_universe(sort * s) {
    SASSERT(m_m.is_uninterp(s));
    return m_universe.contains(s) ? m_universe.find(s).size() : 1;
}

//get universe 
expr * model_constructor::get_universe(mc_context & mc, sort * s, unsigned i) {
    SASSERT(m_m.is_uninterp(s));
    if (!m_universe.contains(s)) {
        SASSERT(i==0);
        ptr_vector<expr> univ;
        univ.push_back(mc.get_some_value(s));
        m_universe.insert(s, univ);
        return univ[0];
    }
    else {
        SASSERT(i<m_universe.find(s).size());
        return m_universe.find(s)[i];
    }
}

projection * model_constructor::get_projection(mc_context & mc, func_decl * f, unsigned i, bool mk_rep) {
    unsigned fid = get_func_id(mc, f);
    projection * p = m_func_arg_proj.find(fid)[i];
    return mk_rep ? p->get_rep() : p;
}

projection * model_constructor::get_projection(mc_context & mc, quantifier * q, unsigned i, bool mk_rep) {
    unsigned qid = get_quantifier_id(mc, q);
    projection * p = m_quant_var_proj.find(qid)[i];
    return mk_rep ? p->get_rep() : p;
}

void model_constructor::get_inst(mc_context & mc, quantifier * q, cond * c, expr_ref_buffer & inst, bool & found_expr) {
    found_expr = true;
    bool used_only_rel_domain = true;
    for (unsigned j=0; j<c->get_size(); j++) {
        abs_val * a = c->get_value(j);
        projection * p = get_projection(mc, q, j, false);
        //first, get offset
        expr * o = p->get_offset();
        expr_ref ie(m_m);
        bool c_found_expr;
        p->get_rep()->get_witness(mc, a, ie, o, c_found_expr);
        inst.push_back(ie);
        found_expr = found_expr && c_found_expr;
    }
}

def * model_constructor::get_projection_definition(mc_context & mc, func_decl * f) {
    def * dp = 0;
    for (unsigned i=0; i<f->get_arity(); i++) {
        projection * p = get_projection(mc, f, i);
        def * dpa = p->get_definition(mc);
        dp = i==0 ? dpa : mc.mk_product(dp, dpa);
        dp->simplify(mc);
    }
    TRACE("rel_domain_projection", tout << "Projection is : " << "\n";
                                   mc.display(tout, dp);
                                   tout << "\n";);
    return dp;
}
