/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    model_repair.cpp

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-04-25.

--*/

#include"model_repair.h"
#include"ast_pp.h"
#include"model_construct.h"
#include"var_subst.h"

//#define REPAIR_DEBUG

using namespace qsolver;

model_repair::model_repair(ast_manager & _m) : m_m(_m){

}

void model_repair::reset_round(mc_context & mc) {
    m_repair_quant.reset();
    m_repair_inst.reset();
    m_repairs_permanent.reset();
    m_active = true; 
    m_tracking = false;//true;
    m_tracking_rec_repair = true;
    //stats
    m_stat_repairs = 0;
}

bool model_repair::repair_formula(mc_context & mc, model_constructor * mct, quantifier * q, expr_ref_buffer & vsub, expr_ref_buffer & tsub, expr_ref_buffer & instantiations) {
    if (m_active) {
        ptr_buffer<annot_entry> fail_entry;
        ptr_buffer<expr> fail_value;
        ptr_buffer<func_decl> fail_func;
        annot_entry * inst_reason = 0;
        if (do_repair_formula(mc, mct, q, q->get_expr(), vsub, tsub, true, fail_entry, fail_value, fail_func, inst_reason)) {
            TRACE("repair_model",tout << "...instantiation for " << mk_pp(q,m_m) << " was repaired.\n";);
#ifdef REPAIR_DEBUG
            //make sure the repair was actually successful...
            expr * v2 = mc.evaluate(mct, q->get_expr(), vsub, true);
            SASSERT(v2);
            SASSERT(m_m.is_true(v2));
#endif
            return true;
        }
        else {
            if (m_tracking) {
                for (unsigned i=0; i<fail_entry.size(); i++) {
                    if (!is_permanent(fail_entry[i])) {
                        TRACE("repair_model_recurse", tout << "Would have been able to repair, if not for : "; mc.display(tout, fail_entry[i]); tout << " in " << mk_pp(fail_func[i],m_m) << "\n";
                                                        tout << "Wanted value was " << mk_pp(fail_value[i], m_m) << "\n";);
                        //now we will undo and try to re-repair
                        //flip this entry to repair the current quantifier
                        fail_entry[i]->m_result = fail_value[i];
                        //tell model constructor that this entry cannot be changed (during the recursion)
                        push_permanent_repair(fail_entry[i]);
                        //must repair all quantifiers previously repaired by this entry
                        SASSERT(m_repair_quant.contains(fail_entry[i]));
                        bool success = true;
                        ptr_vector<quantifier> & qrv = m_repair_quant.find(fail_entry[i]);
                        ptr_vector<annot_entry> & irv = m_repair_inst.find(fail_entry[i]);
                        TRACE("repair_model_recurse", tout << "There are " << qrv.size() << " quantifier instantiations that depended on this entry.\n";);
                        for (unsigned j=0; j<qrv.size(); j++) {
                            quantifier * qr = qrv[j];
                            annot_entry * ir = irv[j];
                            TRACE("repair_model_recurse", tout << "This entry had repaired " << mk_pp(qr,m_m) << " with instantiation "; mc.display(tout, ir); tout << "\n";);
                            //now, try to add the other instantiation
                            expr_ref_buffer instr(m_m); 
                            expr_ref_buffer vsubr(m_m);
                            for (unsigned k=0; k<ir->get_size(); k++) {
                                instr.push_back(ir->get_annotation(k));
                                vsubr.push_back(ir->get_value(k));
                            }
                            if (mc.add_instantiation(mct, qr, instr, vsubr, instantiations, false, true)) {
                                success = false;
                            }
                        }
                        pop_permanent_repair();
                        if (success && m_tracking_rec_repair) {
                            TRACE("repair_model",tout << "...instantiation for " << mk_pp(q,m_m) << "  was recursively repaired.\n";);
                            return true;
                        }
                    }
                }
            }
        }
    }
    return false;
}

//repair model
bool model_repair::do_repair_formula(mc_context & mc, model_constructor * mct, quantifier * q, expr * e, expr_ref_buffer & vsub, expr_ref_buffer & tsub, bool polarity, 
                                  ptr_buffer<annot_entry> & fail_entry, ptr_buffer<expr> & fail_value, ptr_buffer<func_decl> & fail_func, annot_entry * & inst_reason) {
    TRACE("repair_model_debug", tout << "Try repairing " << mk_pp(e,m_m) << ", polarity = " << polarity << "\n";);
    if (is_app(e)) {
        //try to make the formula with var_subst equal to polarity
        if ((m_m.is_or(e) && polarity) || (m_m.is_and(e) && !polarity)) {
            //first do partial evaluation of each argument, then if necessary repair
            sbuffer<unsigned> children_undef;
            sbuffer<unsigned> children_false;
            for (unsigned i=0; i<to_app(e)->get_num_args(); i++) {
                expr * ecv = mc.evaluate(mct, to_app(e)->get_arg(i), vsub, true);
                if (ecv) {
                    if (m_m.is_true(ecv)==polarity) {
                        //already true in partial model, no need to do anything else
                        TRACE("repair_model_debug", tout << "Repaired: Disjunction, no need to repair, " << mk_pp(to_app(e)->get_arg(i), m_m) << " is already true.\n";);
                        return true;
                    }
                    else {
                        children_false.push_back(i);
                    }
                }
                else {
                    children_undef.push_back(i);
                }
            }
            //if we can repair a child
            for( unsigned r=0; r<2; r++) {
                sbuffer<unsigned> & curr_vec = r==0 ? children_undef : children_false;
                for (unsigned i=0; i<curr_vec.size(); i++) {
                    if (do_repair_formula(mc, mct, q, to_app(e)->get_arg(curr_vec[i]), vsub, tsub, polarity, fail_entry, fail_value, fail_func, inst_reason)) {
                        return true;
                    }
                }
            }
            return false;
        }
        else if (m_m.is_not(e)) {
            return do_repair_formula(mc, mct, q, to_app(e)->get_arg(0), vsub, tsub, !polarity, fail_entry, fail_value, fail_func, inst_reason);
        }
        else if (m_m.is_eq(e) || m_m.is_iff(e) || mc.m_au.is_le(e) || mc.m_au.is_ge(e)) { 

            //two iterations
            // on first iteration, check if a side is defined in partial model (this is prefered)
            // on second iteration, check if neither side is defined
            bool processed[2] = {false, false};
            for (unsigned r=0; r<2; r++) {
                for (unsigned i=0; i<2; i++) {
                    if (!processed[i]) {
                        expr * ec = to_app(e)->get_arg(i);
                        if (is_app(ec) && is_uninterp(to_app(ec)->get_decl())) {
                            //evaluate the other side
                            expr * eco = to_app(e)->get_arg(i==0 ? 1 : 0);
                            expr * ecov = 0;
                            if (r==0) {
                                ecov = mc.evaluate(mct, eco, vsub, true); //it must have a definition in the partial model
                            }
                            else {
                                ecov = mc.evaluate(mct, eco, vsub);    //now try full
                            }
                            if (ecov) {
                                processed[i] = true;
                                expr * vcomp = 0;       //the term we are trying to make the term equal to
                                if (polarity) {
                                    vcomp = ecov;
                                }
                                else {
                                    if (m_m.is_iff(e)) {
                                        SASSERT(m_m.is_true(ecov) || m_m.is_false(ecov));
                                        vcomp = m_m.is_true(ecov) ? mc.m_false : mc.m_true;
                                    }
                                    else if (m_m.is_eq(e) || mc.m_au.is_le(e) || mc.m_au.is_ge(e)) {
                                        sort * s = get_sort(ecov);
                                        if (mc.m_au.is_int(s)) {
                                            vcomp = mc.mk_simple_add(ecov, mc.m_au.is_ge(e)==(i==0) ? -1 : 1);
                                        }
                                        else if (m_m.is_uninterp(s)) {
                                            vcomp = mct->get_some_element_universe(mc, s, ecov);
                                        }
                                    }
                                }
                                if (vcomp) {
                                    TRACE("repair_model_debug", tout << "Trying to repair relation with " << (i==0 ? "R" : "L") << "HS equal to " << mk_pp(vcomp,m_m) << "\n";);
                                }
                                if (vcomp && do_repair_term(mc, mct, q, ec, vsub, tsub, vcomp, fail_entry, fail_value, fail_func, inst_reason)) {
                                    //ensure the interpretation of the other side is defined in partial model if necessary
                                    if (r==1) {
                                        expr * ecov2 = ensure_interpretation(mc, mct, eco, vsub, tsub, q, inst_reason); 
                                        if (ecov!=ecov2) {  //this should only happen in rare cases
                                            TRACE("repair_model_warn", tout << "WARNING : While repairing " << mk_pp(e,m_m) << ", trying to ensure interpretation of " << mk_pp(eco,m_m) << ", the value became different.\n";
                                                                        tout << "Before : " << mk_pp(ecov,m_m) << "\n";
                                                                        tout << "After : " << mk_pp(ecov2,m_m) << "\n";);
                                            return false;
                                        }
                                        //SASSERT(ecov==ecov2);
                                    }
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
            //...if can't explicitly find/record repair, fall through to check partial model
        }
        else if (m_m.is_ite(e)) {
            expr * c = mc.evaluate(mct, to_app(e)->get_arg(0), true);  //it must have a definition in the partial model
            if (c) {
                SASSERT(m_m.is_true(c) || m_m.is_false(c));
                //first try to repair children
                for (unsigned i=0; i<2; i++) {
                    if (m_m.is_true(c)==(i==0)) {
                        if (do_repair_formula(mc, mct, q, to_app(e)->get_arg(i+1), vsub, tsub, polarity, fail_entry, fail_value, fail_func, inst_reason)) {
                            return true;
                        }
                    }
                }
            }
            //try to repair condition
            expr * ec = mc.evaluate(mct, to_app(e)->get_arg(m_m.is_true(c) ? 2 : 1), vsub, true);
            //check if the other child is favorable
            if (ec && m_m.is_true(ec)==polarity) {
                if (do_repair_formula(mc, mct, q, to_app(e)->get_arg(0), vsub, tsub, !m_m.is_true(c), fail_entry, fail_value, fail_func, inst_reason)) {
                    return true;
                }
            }
            return false;
        }
        else if (is_uninterp(to_app(e)->get_decl())) {
            //predicate case (easy)
            return do_repair_term(mc, mct, q, e, vsub, tsub, polarity ? mc.m_true : mc.m_false, fail_entry, fail_value, fail_func, inst_reason);
        }

        //last chance is to look at partial model (this will happen for or's with false polarity, or unknown literal types)
        expr * ecv = mc.evaluate(mct, e, vsub, true);
        if (ecv && ((m_m.is_true(ecv) && polarity) || (m_m.is_false(ecv) && !polarity))) {
            TRACE("repair_model_debug", tout << "Repaired: The partial evaluation of " << mk_pp(e,m_m) << " happens to be correct.\n";);
            return true;
        }
    }
    return false;
}

bool model_repair::do_repair_term(mc_context & mc, model_constructor * mct, quantifier * q, expr * t, expr_ref_buffer & vsub, expr_ref_buffer & tsub, expr * v, 
                               ptr_buffer<annot_entry> & fail_entry, ptr_buffer<expr> & fail_value, ptr_buffer<func_decl> & fail_func, annot_entry * & inst_reason) {
    //try to make the term with var_subst equal to v
    SASSERT(is_uninterp(t));
    // evaluate the arguments in the complete model
    expr_ref_buffer args(m_m);
    for (unsigned i=0; i<to_app(t)->get_num_args(); i++) {
        expr * vc = mc.evaluate(mct, to_app(t)->get_arg(i), vsub);
        if (!vc) return false;
        args.push_back(vc);
    }
    func_decl * f = to_app(t)->get_decl();
    //SASSERT(is_uninterp(f));
    simple_def * df = mct->get_simple_def(mc, f);
    //see if the entry exists in df
    annot_entry * tae = df->get_entry(args);
    if ((tae && tae->get_result()==v) || !tae) {
        //it will be repaired, will need to record this instantiation
        if (m_tracking && !inst_reason) {
            inst_reason = mc.mk_annot_entry(vsub, tsub, mc.m_true);
        }
        if (tae) {
            // if any has smaller depth, replace?
            /*
            for (unsigned i=0; i<to_app(t)->get_num_args(); i++) {
                expr * ec = to_app(t)->get_arg(i);
                if (is_var(ec)) {
                    TRACE("repair_model_debug", tout << "Compare depth of " << mk_pp(tsub[(q->get_num_decls()-1)-to_var(ec)->get_idx()], m_m) << " and " << mk_pp(tae->get_annotation(i),m_m) << "\n";);
                }
            }
            */
            //already true in partial model, no need to do anything
            if (m_tracking && df->is_repair_entry(tae)) {
                //mark that you depend on this entry
                append_repair(tae, q, inst_reason);
            }
            TRACE("repair_model_debug", tout << "Repaired: Uninterpreted function, no need to repair, the value of " << mk_pp(t,m_m) << " is already correct.\n";);
        }
        else {
            expr_ref ts(m_m);
            var_subst vs(m_m);
            vs(t,tsub.size(),tsub.c_ptr(), ts);
            if (!mc.m_expr_produced.contains(ts)) {
                mc.m_expr_produced.push_back(ts);
            }

            // do the repair
            annot_entry * c = mc.mk_annot_entry(args, ts, v);
            TRACE("repair_model", tout << "Can be fixed by adding ";
                                  mc.display(tout,c);
                                  tout << " to " << mk_pp(f,m_m) << "\n";);
            TRACE("repair_model_debug", tout << "variable substitution is : \n";
                                        for (unsigned i=0; i<vsub.size(); i++) {
                                            tout << "   " << mk_pp(tsub[(vsub.size()-1)-i], m_m) << ", value = "; mc.display(tout, vsub[i]);
                                            expr * ve = mc.evaluate(mct,tsub[(vsub.size()-1)-i],vsub);
                                            SASSERT(ve==vsub[i]);
                                            tout << ", evaluated = "; mc.display(tout,ve); tout << "\n";
                                        }
                                        );
            append_entry_to_simple_def(mc, mct, f, c, q, inst_reason);
        }
        //then, make sure all entries are produced by ground entries
        for (unsigned i=0; i<to_app(t)->get_num_args(); i++) {
            expr * env = ensure_interpretation(mc, mct, to_app(t)->get_arg(i), vsub, tsub, q, inst_reason);
            if (env!=args[i]) { //if a previous model repair messed up this one, fail.  this should only happen on corner cases
                TRACE("repair_model_debug_warn", tout << "WARNING : could not ensure interpretation of " << mk_pp(to_app(t)->get_arg(i),m_m) << "\n";);
                return false;
            }
        }
        return true;
    }
    else {
        //if it was made by another repair, we might want to investigate further
        if (m_tracking && df->is_repair_entry(tae)) {
            fail_entry.push_back(tae);
            fail_value.push_back(v);
            fail_func.push_back(f);
        }
        return false;
    }
}

//this function is a quick way to ensure PM[[t]] = M[[t]], it is in theory equivalent to repair( t, M[[t]] )
expr * model_repair::ensure_interpretation(mc_context & mc, model_constructor * mct, expr * e, expr_ref_buffer & vsub, expr_ref_buffer & tsub,
                                           quantifier * q_reason, annot_entry * inst_reason) {
    //if it is undefined in the partial model
    expr * ev = mc.evaluate(mct, e, vsub, true);
    if (!ev) {
        SASSERT(is_app(e));
        //ensure the interpretation of children
        expr_ref_buffer children(m_m);
        for (unsigned i=0; i<to_app(e)->get_num_args(); i++) {
            expr * vc = ensure_interpretation(mc, mct, to_app(e)->get_arg(i), vsub, tsub, q_reason, inst_reason);
            if (!vc) {
                return 0;
            }
            else {
                children.push_back(vc);
            }
        }
        func_decl * f = to_app(e)->get_decl();
        if (is_uninterp(e)) {
            //if undefined in the function, add an entry
            simple_def * df  = mct->get_simple_def(mc, f);
            ev = df->evaluate(children, true);
            if (!ev) {
                //need to make the term
                expr_ref ts(m_m);
                var_subst vs(m_m);
                vs(e,tsub.size(),tsub.c_ptr(), ts);
                if (!mc.m_expr_produced.contains(ts)) {
                    mc.m_expr_produced.push_back(ts);
                }
                annot_entry * c = mc.mk_annot_entry(children, ts, df->get_else());
                TRACE("repair_model_debug", tout << "Append entry to ensure evaluation in partial model : "; mc.display(tout, c); tout << " of " << mk_pp(e,m_m) << ".\n";);
                SASSERT(!m_tracking || inst_reason);
                append_entry_to_simple_def(mc, mct, f, c, q_reason, inst_reason);
                ev = df->get_else();
            }
        }
        else {
            ev = mc.evaluate_interp(f, children);
        }
    }
    return ev;
}


bool model_repair::append_entry_to_simple_def(mc_context & mc, model_constructor * mct, func_decl * f, annot_entry * c,
                                              quantifier * q_repair, annot_entry * inst_repair) {
    SASSERT(is_uninterp(f));
    simple_def * sdf  = mct->get_simple_def(mc, f);
    if (sdf->append_entry(mc, c, true)) {
        m_was_repaired = true;
        m_stat_repairs++;
        TRACE("repair_model_mct", tout << "Added "; mc.display(tout, c); tout << " to " << mk_pp(f, m_m) << "\n";);
        //make sure it is in relevant domain
        for (unsigned i=0; i<f->get_arity(); i++) {
            projection * p = mct->get_projection(mc, f, i);
            SASSERT(c->get_value(i));
            val * vi = mc.mk_val(c->get_value(i));
            if (!p->has_relevant_domain_val(vi)) {
                expr * ei = c->get_annotation(i);
                p->add_relevant_domain(ei, vi);
            }
        }
        append_repair(c, q_repair, inst_repair);
        //clear evaluation caches
        mc.m_evaluations.reset(); 
        mc.m_partial_evaluations.reset();
        return true;
    }
    return false;
}

void model_repair::append_repair(annot_entry * c, quantifier * q_repair, annot_entry * inst_repair) {
    if (q_repair && inst_repair) {
        if (m_repair_quant.contains(c)) {
            ptr_vector<quantifier> & qvec = m_repair_quant.find(c);
            ptr_vector<annot_entry> & ivec = m_repair_inst.find(c);
            qvec.push_back(q_repair);
            ivec.push_back(inst_repair);
        }
        else {
            ptr_vector<quantifier> qvec;
            ptr_vector<annot_entry> ivec;
            qvec.push_back(q_repair);
            ivec.push_back(inst_repair);
            m_repair_quant.insert(c, qvec);
            m_repair_inst.insert(c, ivec);
        }
    }
}
