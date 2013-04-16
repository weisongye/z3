/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    classify_quantifier.cpp

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-04-04.

--*/

#include"classify_quantifier.h"
#include"ast_pp.h"
#include"model_construct.h"

using namespace qsolver;

classify_util::classify_util(ast_manager & m, arith_util & au, bv_util & bvu) :
m_m(m), m_au(au), m_bvu(bvu) {

}

bool classify_util::is_atomic_value(expr * e) {
    return m_au.is_numeral(e) || m_m.is_true(e) || m_m.is_false(e) || m_bvu.is_numeral(e);   
}

bool classify_util::is_var_negated(expr * e, var * & v) {
    expr * ev;
    if (m_au.is_times_minus_one(e, ev)) {
        if (is_var(ev)) {
            v = to_var(ev);
            return true;
        }
    }
    //TODO: do for bitvectors?
    return false;
}

bool classify_util::is_var_atom(expr * e) {
    var * v;
    bool isn;
    return is_var_atom(e, v, isn);
}

bool classify_util::is_var_atom(expr * e, var * & v, bool & is_negated) {
    if (is_var(e)) {
        v = to_var(e);
        is_negated = false;
        return true;
    }
    else if (is_var_negated(e, v)) {
        is_negated = true;
        return true;
    }
    return false;
}

bool classify_util::is_var_offset(expr * e, var * & v, expr_ref & offset, bool & is_negated, unsigned req, bool mk_offset) {
    if (is_var_atom(e, v, is_negated)) {
        offset = 0;
        return true;
    }
    else if (m_au.is_add(e) || m_bvu.is_bv_add(e)) {
        bool foundVar = false;
        unsigned varIndex;
        for (unsigned i=0; i<to_app(e)->get_num_args(); i++) {
            expr * ec = to_app(e)->get_arg(i);
            if (is_var_atom(ec, v, is_negated)) {
                if (req!=REQ_NONE && foundVar) {
                    v = 0;
                    return false;
                }
                foundVar = true;
                varIndex = i;
            }
            else if (req==REQ_GROUND && !is_ground(ec)) {
                v = 0;
                return false;
            }
        }
        if (foundVar) {
            if (mk_offset) {
                //make the offset
                ptr_buffer<expr> sum;
                for (unsigned i=0; i<to_app(e)->get_num_args(); i++) {
                    expr * ec = to_app(e)->get_arg(i);
                    if (varIndex!=i) {
                        sum.push_back(ec);
                    }
                }
                if (sum.empty()) {
                    offset = 0;
                }
                else if (sum.size()==1) {
                    offset = sum[0];
                }
                else {
                    offset = m_au.is_add(e) ? m_au.mk_add(sum.size(), sum.c_ptr()) : m_bvu.mk_bv_add(sum.size(), sum.c_ptr());
                }
            }
            return true;
        }
    }
    return false;
}


bool classify_util::is_var_offset(expr * e, unsigned req) {
    var * v;
    expr_ref offset(m_m);
    bool is_negated;
    return is_var_offset(e, v, offset, is_negated, req, false);

}

//is variable with offset?
bool classify_util::is_var_offset(expr * e, var * & v, expr_ref & offset, bool & is_negated, unsigned req) {
    return is_var_offset(e, v, offset, is_negated, req, true);
}

//is variable with relation with term?
bool classify_util::is_var_relation(expr * e, var * & v, expr_ref & t, bool & is_flipped, unsigned req, bool mk_t) {
    if (!is_uninterp(e) && is_app(e) && to_app(e)->get_num_args()==2) {
        func_decl * f = to_app(e)->get_decl();
        //check if it is a proper relation
        bool opReq = false;
        if (m_m.is_eq(f)) {
            opReq = true;
        }
        else if (f->get_family_id()==m_au.get_family_id()) {
            //strict inequalities should be simplified away
            SASSERT(f->get_decl_kind()!=OP_GT && f->get_decl_kind()!=OP_LT);
            if (f->get_decl_kind()==OP_GE || f->get_decl_kind()==OP_LE) {
                opReq = true;
            }
        }
        else if (f->get_family_id()==m_bvu.get_family_id()) {
            //TODO
            SASSERT(f->get_decl_kind()!=OP_UGT && f->get_decl_kind()!=OP_ULT);
            if (f->get_decl_kind()==OP_UGEQ || f->get_decl_kind()==OP_ULEQ) {
                opReq = true;
            }
        }
        if (opReq) {
            v = 0;
            //check to see if one of the children is a variable
            unsigned varIndex;
            expr_ref offset(m_m);
            for (unsigned i=0; i<2; i++) {
                if (is_var_offset(to_app(e)->get_arg(i), v, offset, is_flipped, req)) {
                    varIndex = i;
                    break;
                }
            }
            if (v) {
                //check if the other term meets the requirement
                t = to_app(e)->get_arg(varIndex==0 ? 1 : 0);
                if (req!=REQ_NONE) {
                    if (!is_ground(t)) {
                        if (req==REQ_GROUND) {
                            return false;
                        }
                        else if (is_var_offset(t)) {
                            SASSERT(req==REQ_NON_VARIABLE);
                            return false;
                        }
                    }
                }
                if (mk_t) {
                    sort * st = get_sort(t);
                    bool is_int = m_au.is_int(st);
                    bool is_bv = m_bvu.is_bv_sort(st);
                    expr * move_t = 0;
                    if (is_flipped) {
                        //move t to other side
                        move_t = t;
                        t = offset;
                        if (m_m.is_eq(e)) {
                            is_flipped = false;
                        }
                    }
                    else {
                        //move offset to other side
                        move_t = offset;
                    }
                    if (move_t) {
                        //negate move_t, add to t
                        if ((is_int && m_au.is_zero(move_t)) || (is_bv && m_bvu.is_zero(move_t))) {
                            t = t ? t : move_t;
                        }
                        else {
                            if (is_int) {
                                expr * mtv;
                                move_t = m_au.is_times_minus_one(move_t, mtv) ? mtv : m_au.mk_mul(m_au.mk_numeral(rational(-1), true), move_t);
                                t = (t && !m_au.is_zero(t)) ? m_au.mk_add(t, move_t) : move_t;
                            }
                            else {
                                return false;
                            }
                        }
                    }
                    SASSERT(t);
                }
                return true;
            }
        }
    }
    return false;
}

//is variable with operation with non-variable term?
bool classify_util::is_var_relation(expr * e, unsigned req) {
    var * v;
    expr_ref t(m_m);
    bool is_flipped;
    return is_var_relation(e, v, t, is_flipped, req, false);
}

//is variable with operation with non-variable term?  return function if so
bool classify_util::is_var_relation(expr * e, var * & v, expr_ref & t, bool & is_flipped, unsigned req) {
    bool ret = is_var_relation(e, v, t, is_flipped, req, true);
    if (ret) {
        TRACE("classify_var_relation_debug", tout << "Formula " << mk_pp(e,m_m) << " can be classified as variable relation :  (requirement=" << req << ") \n";
                                            tout << "  " << mk_pp(v,m_m) << " ~ " << mk_pp(t,m_m) << ", relation flipped = " << is_flipped << "\n";);
    }
    return ret;
}

bool classify_util::is_witnessable(expr * e, bool hasPolarity, bool polarity, 
                                   var * & v1, var * & v2, ptr_vector<expr> & no_proj_terms, expr_ref_buffer & rel_domain, unsigned & proj_type, bool mk_rd, 
                                   bool req_exact) {
    expr_ref t(m_m); 
    bool is_flipped;
    if (is_var_relation(e, v1, t, is_flipped)) {
        //TRACE("rel_domain_debug", tout << "check witnessable : " << mk_pp(e,m_m) << " " << mk_pp(v1,m_m) << " " << mk_pp(t, m_m) << " " << req_exact << std::endl;);
        if (m_m.is_eq(e)) {
            //should have applied DER
            //SASSERT(!hasPolarity || polarity);
            if (is_ground(t)) {
                if (mk_rd) {
                    no_proj_terms.push_back(t);
                    sort * st = get_sort(t);
                    //t-1 and t+1 are in relevant domain
                    if (m_au.is_int(st) || m_bvu.is_bv_sort(st)) {
                        for (unsigned r=0; r<2; r++) {
                            expr_ref rel_expr(m_m);
                            if (m_au.is_int(st)) {
                                rel_expr = m_au.mk_add(t, m_au.mk_numeral(rational(r==0 ? 1 : -1), true));
                            }
                            else if (m_bvu.is_bv_sort(st)) {
                                unsigned sz = m_bvu.get_bv_size(st);
                                rel_expr = m_bvu.mk_bv_add(t, m_bvu.mk_numeral(rational(r==0 ? 1 : -1), sz));
                            }
                            rel_domain.push_back(rel_expr);
                        }
                    }
                    if (!hasPolarity || polarity) {
                        rel_domain.push_back(t);
                    }
                }
                return !req_exact || (hasPolarity && !polarity);
            }
            else {
                //TODO?
                //case where x=f(x) or x=f(y)
            }
        }
        else {
            //projection must be monotonic
            proj_type = projection::PROJ_MONOTONIC;
            if (is_ground(t)) {
                if (mk_rd) {
                    //some of t+-1 will be added to relevant domain
                    for (unsigned p=0; p<2; p++) {
                        if (!hasPolarity || polarity==(p==1)) {
                            //process at polarity (p==1)
                            expr_ref rel_expr(m_m);
                            bool isStrict = (m_au.is_lt(e) || m_au.is_gt(e))==(p==0);
                            if (isStrict) {
                                bool isGreater = ((m_au.is_ge(e) || m_au.is_gt(e))==(p==1))==is_flipped;
                                rational r(isGreater ? 1 : -1);
                                rel_expr = m_au.mk_add(t, m_au.mk_numeral(r,true));
                            }
                            else {
                                rel_expr = t;
                            }
                            rel_domain.push_back(rel_expr);
                        }
                    }
                }
                return !req_exact || (hasPolarity && !polarity);
            }
            else if (is_var(t)) {
                v2 = to_var(t);
                return !req_exact || (hasPolarity && !polarity);
            }
            else {
                //TODO
                //case where x>=f(x) or x>=f(y)
                return !req_exact;
            }
        }
    }
    return false;
}

bool classify_util::is_witnessable(expr * e, bool hasPolarity, bool polarity, bool req_exact) {
    var * v1;
    var * v2;
    ptr_vector<expr> no_proj_terms;
    expr_ref_buffer rel_domain(m_m);
    unsigned proj_type;
    return is_witnessable(e, hasPolarity, polarity, v1, v2, no_proj_terms, rel_domain, proj_type, false, req_exact);
}

bool classify_util::is_witnessable(expr * e, bool hasPolarity, bool polarity, 
                                   var * & v1, var * & v2, ptr_vector<expr> & no_proj_terms, expr_ref_buffer & rel_domain, unsigned & proj_type, bool req_exact){
    return is_witnessable(e, hasPolarity, polarity, v1, v2, no_proj_terms, rel_domain, proj_type, true, req_exact);
}

classify_info::classify_info(ast_manager & m, arith_util & au, bv_util & bvu, quantifier* q, bool use_monotonic_projections) :
    m_m(m), m_au(au), m_bvu(bvu), m_util(m, au, bvu), m_q(q, m), m_lits(m) {
    m_use_monotonic_projections = use_monotonic_projections;
}

void classify_info::classify_term(expr * e, bool hasPolarity, bool polarity, bool & model_checkable, bool & witnessable, bool & ground_result) {
    if (is_app(e)) {
        bool cHasPolarity = hasPolarity && !m_m.is_iff(e);    //ITE handled below
        bool cPolarity = m_m.is_not(e) ? !polarity : polarity;

        model_checkable = true;
        witnessable = true;
        bool children_model_checkable = true;
        bool children_witnessable = true;
        for (unsigned i=0; i<to_app(e)->get_num_args(); i++) {
            expr * ec = to_app(e)->get_arg(i);
            expr_ref_buffer gtc(m_m);
            bool cmc = true;
            bool cw = true;
            bool cgr;
            bool cHasPolarity2 = cHasPolarity && (!m_m.is_ite(e) || i!=0);
            classify_term(ec, cHasPolarity2, cPolarity, cmc, cw, cgr);
            children_model_checkable = children_model_checkable && cmc;
            children_witnessable = children_witnessable && cw;
            if (!cgr && !is_uninterp(e)) {
                TRACE("classify_debug", tout << "Term is bad in " << mk_pp(e,m_m) << "\n";);
                cmc = false;
                cw = false;
            }
            //if (!cw && is_uninterp(e)) {
                //TODO: check if it is variable offset child of uninterpreted  (this is problematic since CC+offsets for projections can be inconsistent)
                //var * v;
                //expr_ref offset(m_m);
                //bool is_negated;
                //if (m_util.is_var_offset(ec, v, offset, is_negated, classify_util::REQ_GROUND)) {
                //}
            //}
            model_checkable = model_checkable && cmc;
            witnessable = witnessable && cw;
            ground_result = ground_result && cgr;
        }
        if (!model_checkable && children_model_checkable) {
            if (m_util.is_var_offset(e, classify_util::REQ_NON_VARIABLE)) {
                TRACE("classify_debug", tout << "Term is actually model-checkable : " << mk_pp(e,m_m) << "\n";);
                model_checkable = true;
            }
            if ((m_use_monotonic_projections || m_m.is_eq(e)) && m_util.is_var_relation(e, classify_util::REQ_NON_VARIABLE)) {
                TRACE("classify_debug", tout << "Term is actually model-checkable : " << mk_pp(e,m_m) << "\n";);
                model_checkable = true;
                ground_result = true;
            }
            //TODO: x=y for uninterpreted sorts
            //if (m_m.is_eq(e) && m_m.is_uninterp(get_sort(to_app(e)->get_arg(0)))) {
            //    TRACE("classify_debug", tout << "Term is actually model-checkable : " << mk_pp(e,m_m) << "\n";);
            //    model_checkable = true;
            //    ground_result = true;
            //}
        }
        if (!witnessable && children_witnessable) {
            if (m_util.is_witnessable(e, hasPolarity, polarity)) {
                TRACE("classify_debug", tout << "Term is actually witnessable : " << mk_pp(e,m_m) << "\n";);
                witnessable = true;
            }
        }
        if (is_uninterp(e)) {
            ground_result = true;
        }
        TRACE("classify_debug", tout << "Classified " << mk_pp(e,m_m) << " as : gr=" << ground_result << ", mc=" << model_checkable << ", w=" << witnessable << "\n";);
    }
    else if (m_util.is_atomic_value(e)) {
        model_checkable = true;
        witnessable = true;
        ground_result = true;
    }
    else if (is_var(e)) {
        model_checkable = true;
        witnessable = true;
        ground_result = false;
    }
    else {
        model_checkable = false;
        witnessable = false;
        ground_result = false;
    }
}

bool classify_info::compute() {
    TRACE("classify", tout << "Classifying " << mk_pp(m_q->get_expr(),m_m) << "\n";);
    //collect literals from body of quantifier
    //we assume it is in NNF, body should be unit or an "or"
    if (m_m.is_or(m_q->get_expr())) {
        m_lits.append(to_app(m_q->get_expr())->get_num_args(), to_app(m_q->get_expr())->get_args());
    }
    else {
        m_lits.push_back(m_q->get_expr());
    }
    //classify each literal
    for (unsigned i=0; i<m_lits.size(); i++) {
        bool model_checkable;
        bool witnessable;
        bool ground_result;
        classify_term(m_lits[i], true, true, model_checkable, witnessable, ground_result);
        if (model_checkable) {
            m_mc_lits.push_back(m_lits[i]);
        }
        if (witnessable) {
            m_w_lits.push_back(m_lits[i]);
        }
    }
    return true;
}

//get model-checkable
void classify_info::get_model_checkable(expr_ref & e, bool req_witnessable) {
    if (!req_witnessable) {
        e = m_mc_lits.size()>1 ? m_m.mk_or(m_mc_lits.size(), m_mc_lits.c_ptr()) : (m_mc_lits.size()==1 ? m_mc_lits[0] : m_m.mk_false());
    }
    else {
        ptr_vector<expr> lits;
        for (unsigned i=0; i<m_mc_lits.size(); i++) {
            if (m_w_lits.contains(m_mc_lits[i])) {
                lits.push_back(m_mc_lits[i]);
            }
        }
        e = lits.size()>1 ? m_m.mk_or(lits.size(), lits.c_ptr()) : (lits.size()==1 ? lits[0] : m_m.mk_false());
    }
}

//get witnessable
void classify_info::get_witnessable(expr_ref & e, bool req_non_model_checkable) {
    if (!req_non_model_checkable) {
        e = m_w_lits.size()>1 ? m_m.mk_or(m_w_lits.size(), m_w_lits.c_ptr()) : (m_w_lits.size()==1 ? m_w_lits[0] : m_m.mk_false());
    }
    else {
        ptr_vector<expr> lits;
        for (unsigned i=0; i<m_w_lits.size(); i++) {
            if (!m_mc_lits.contains(m_w_lits[i])) {
                lits.push_back(m_w_lits[i]);
            }
        }
        e = lits.size()>1 ? m_m.mk_or(lits.size(), lits.c_ptr()) : (lits.size()==1 ? lits[0] : m_m.mk_false());
    }
}

void classify_info::display(std::ostream & out) {
    out << "Quantifier " << mk_pp(m_q, m_m) << " can be classified : \n";
    /*
    out << "  Model-checkable portion : ";
    expr_ref mc(m_m);
    get_model_checkable(mc);
    out << mk_pp(mc,m_m) << "\n";
    out << "  Witness-constructable portion : ";
    expr_ref w(m_m);
    get_witnessable(w);
    out << mk_pp(w,m_m) << "\n";
    */
    for (unsigned i=0; i<m_lits.size(); i++) {
        out << "  " << mk_pp(m_lits[i], m_m) << " : ";
        if (m_mc_lits.contains(m_lits[i])) {
            out << "model-checkable ";
            if (m_w_lits.contains(m_lits[i])) {
                out << "and ";
            }
        }
        if (m_w_lits.contains(m_lits[i])) {
            out << "witness-constructable";
        }
        else if(!m_mc_lits.contains(m_lits[i])) {
            out << "bad";
        }
        out << "\n";
    }
}
