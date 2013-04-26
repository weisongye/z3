/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    model_check.cpp

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-04-02.

--*/

#include"model_check.h"
#include"model_construct.h"
#include"ast_pp.h"
#include"var_subst.h"
#include"full_model_check.h"

//#define MODEL_CHECK_DEBUG

using namespace qsolver;

bool inst_trie::add(mc_context & mc, ptr_vector<expr> & inst, unsigned i) {
    if (i==inst.size()) {
        if (m_data) {
            return false;
        }
        else {
            m_data = true;
            return true;
        }
    }
    else {
        inst_trie * it;
        if (!m_inst.find(inst[i],it)) {
            void * mem = mc.allocate(sizeof(inst_trie));
            it = new (mem) inst_trie;
            m_inst.insert(inst[i], it);
        }
        return it->add(mc, inst, i+1);
    }
}

bool inst_trie::add(mc_context & mc, expr_ref_buffer & inst, unsigned i) {
    if (i==inst.size()) {
        if (m_data) {
            return false;
        }
        else {
            m_data = true;
            return true;
        }
    }
    else {
        inst_trie * it;
        if (!m_inst.find(inst[i],it)) {
            void * mem = mc.allocate(sizeof(inst_trie));
            it = new (mem) inst_trie;
            m_inst.insert(inst[i], it);
        }
        return it->add(mc, inst, i+1);
    }
}


mc_context::mc_context(ast_manager & _m) 
    : m_m(_m), m_au(_m), m_bvu(_m), m_ar(_m), m_bvr(_m), m_cutil(_m, m_au, m_bvu), m_expr_produced_global(_m), m_expr_produced(_m) {
    m_true = m_m.mk_true();
    m_false = m_m.mk_false();
    m_simplification = false;
    m_evaluation_cache_active = false;
}

void mc_context::reset_round() {
    m_star = 0;
    m_inst_trie.reset();

    //clear the caches
    m_expr_to_val.reset();
    m_val_to_abs_val.reset();
    m_quant_to_cond_star.reset();
    m_val_to_value_tuple.reset();
    m_expr_produced.reset();
    m_size_to_star.reset();
    m_evaluation_cache_active = false;
    m_evaluations.reset();
    m_partial_evaluations.reset();
    m_ground_evaluations.reset();
    m_ground_partial_evaluations.reset();

    m_reg.reset();
}

//push user context
void mc_context::push() {
    
}

//pop user context
void mc_context::pop() {
    //m_classify_info.reset();
    m_sort_to_dist_expr.reset();
    m_expr_produced_global.reset();

}


val * mc_context::get_bound(abs_val * a, bool isLower) {
    if (a->is_value()) {
        return to_value(a)->get_value();
    }
    else if (a->is_interval()) {
        return isLower ? to_interval(a)->get_lower() : to_interval(a)->get_upper();
    }
    else if (a->is_star()) {
        return 0;
    }
    SASSERT(false);
    return 0;
}

val * mc_context::mk_val(expr* e) {
    if (m_expr_to_val.contains(e)) {
        return m_expr_to_val.find(e); 
    }
    else {
        val * v;
        rational val_r;
        unsigned bvs;
        if (m_au.is_numeral(e, val_r)) {
            v = mk_val(val_r);
        }
        else if (m_bvu.is_numeral(e,val_r,bvs)) {
            v = mk_val(val_r,bvs);
        }
        else{
            void * mem = allocate(sizeof(v_expr));
            v = new (mem) v_expr(e);
        }
        v->m_expr = e;
        m_expr_to_val.insert(e,v);
        if (!m_expr_produced.contains(e)) {
            m_expr_produced.push_back(e);
        }
        return v;
    }
}

val * mc_context::mk_offset(val * v1, val * v2) {
    return mk_canon(mk_add(v1, v2));
}

val * mc_context::mk_val(const rational & r) {
    return mk_val(r.to_mpq().numerator());
}

val * mc_context::mk_val(const mpz & a) {
    void * mem = allocate(sizeof(v_int));
    v_int * vi = new (mem) v_int;
    m_zm.set(vi->m_value, a);
    return vi;
}

val * mc_context::mk_val(const rational & r, unsigned bvs) {
    return mk_val(r.to_mpq().numerator(), bvs);
}

val * mc_context::mk_val(const mpz & a, unsigned bvs) {
    void * mem = allocate(sizeof(v_bv));
    v_bv * vbv = new (mem) v_bv(bvs);
    m_zm.set(vbv->m_value, a);
    return vbv;
}

val * mc_context::mk_val(var * v, val * o, bool isn) {
    void * mem = allocate(sizeof(v_var_offset));
    v_var_offset * vvo = new (mem) v_var_offset(v, o, isn);
    return vvo;
}

val * mc_context::mk_add(val * v1, val * v2) {
    SASSERT(v1->get_kind()==v2->get_kind());
    SASSERT(!v1->is_bv() || to_bv(v1)->get_size()==to_bv(v2)->get_size());
    if (is_zero(v1)) {
        return v2;
    }
    else if (is_zero(v2)) {
        return v1;
    }
    else {
        if (v1->is_int()) {
            mpz curr;
            m_zm.add(to_int(v1)->get_value(), to_int(v2)->get_value(), curr);
            return mk_val(curr);
        }
        else if (v1->is_bv()) {
            mpz curr;
            m_zm.add(to_bv(v1)->get_value(), to_bv(v2)->get_value(), curr);
            return mk_val(curr, to_bv(v1)->get_size());
        }
        else {
            SASSERT(false);
            return 0;
        }
    }
}

val * mc_context::mk_negate(val * v) {
    if (v->is_int()) {
        if (m_zm.is_zero(to_int(v)->get_value())) {
            return v;
        }
        else {
            mpz curr(-1);
            m_zm.mul(curr, to_int(v)->get_value(), curr);
            return mk_val(curr);
        }
    }
    else if (v->is_bv()) {
        if (m_zm.is_zero(to_bv(v)->get_value())) {
            return v;
        }
        else {
            mpz curr(-1);
            m_zm.mul(curr, to_bv(v)->get_value(), curr);
            return mk_val(curr, to_bv(v)->get_size());
        }
    }
    else if (v->is_expr()) {
        return mk_val(m_au.mk_mul(m_au.mk_numeral(rational(-1),true),to_expr(v)->get_value()));
    }
    else {
        SASSERT(false);
        return 0;
    }
}

abs_val * mc_context::mk_offset(abs_val * a, val * v) {
    SASSERT(v);
    if (a->is_star()) {
        return a;
    }
    else if (a->is_value()) {
        return mk_value(mk_add(to_value(a)->get_value(), v));
    }
    else if (a->is_interval()) {
        val * nb[2];
        for (unsigned i=0; i<2; i++) {
            val * b = get_bound(a, i==0);
            nb[i] = b ? mk_add(b, v) : b;
        }
        return mk_interval(nb[0], nb[1]);
    }
    else {
        SASSERT(false);
        return 0;
    }
}

abs_val * mc_context::mk_negate(abs_val * a) {
    if (a->is_star()) {
        return a;
    }
    else if (a->is_value()) {
        return mk_value(mk_negate(to_value(a)->get_value()));
    }
    else if (a->is_interval()) {
        val * nb[2];
        for (unsigned i=0; i<2; i++) {
            val * b = get_bound(a, i==0);
            nb[i==0 ? 1 : 0] = b ? mk_negate(b) : b;
        }
        return mk_interval(nb[0], nb[1]);
    }
    else {
        SASSERT(false);
        return 0;
    }
}


value_tuple * mc_context::mk_value_tuple(val * v) {
    value_tuple * vt;
    if (!m_val_to_value_tuple.find(v,vt)) {
        vt = value_tuple::mk(*this, 1);
        vt->m_vec[0] = v;
        m_val_to_value_tuple.insert(v,vt);
        return vt;
    }
    return vt;
}

value_tuple * mc_context::mk_value_tuple(ptr_buffer<val> & vals) {
    value_tuple * vt = value_tuple::mk(*this, vals.size());
    for (unsigned i=0; i<vals.size(); i++) {
        vt->m_vec[i] = vals[i];
    }
    return vt;
}

value_tuple * mc_context::mk_concat(value_tuple * vt1, value_tuple * vt2) {
    value_tuple * v = value_tuple::mk(*this, vt1->get_size() + vt2->get_size());
    unsigned index = 0;
    for( unsigned k=0; k<vt1->get_size(); k++ ){
        v->m_vec[index] = vt1->m_vec[k];
        index++;
    }
    for( unsigned k=0; k<vt2->get_size(); k++ ){
        v->m_vec[index] = vt2->m_vec[k];
        index++;
    }
    return v;
}


bool mc_context::is_zero(val * v) {
    if (v->is_int()) {
        return m_zm.is_zero(to_int(v)->get_value());
    }
    else if (v->is_bv()) {
        return m_zm.is_zero(to_bv(v)->get_value());
    }
    else {
        SASSERT(false);
        return false;
    }
}

bool mc_context::is_lt(val * v1, val * v2, bool isLower) {
    SASSERT(!v1 || !v2 || v1->get_kind()==v2->get_kind());
    if (v1==v2) {
        return false;
    }else if (v1 && v2) {
        if (v1->is_int()) {
            return m_zm.lt(to_int(v1)->get_value(), to_int(v2)->get_value());
        }else if (v1->is_bv()) {
            SASSERT(to_bv(v1)->get_size()==to_bv(v2)->get_size());
            return m_zm.lt(to_bv(v1)->get_value(), to_bv(v2)->get_value());
        }else {
            SASSERT(false);
            return false;
        }
    }
    else{
        //case v1 = -INF, or v2 = +INF
        return (!v1 && isLower) || (!v2 && !isLower);
    }
}

bool mc_context::is_eq(const rational & r1, const rational & r2) {
    return m_zm.eq(r1.to_mpq().numerator(), r2.to_mpq().numerator());
}

bool mc_context::is_eq(val * v1, val * v2) {
    SASSERT(v1->get_kind()==v2->get_kind());
    if (v1==v2) {
        return true;
    }
    else if (v1->is_int()) {
        return m_zm.eq(to_int(v1)->get_value(), to_int(v2)->get_value());
    }else if (v1->is_bv()) {
        SASSERT(to_bv(v1)->get_size()==to_bv(v2)->get_size());
        return m_zm.eq(to_bv(v1)->get_value(), to_bv(v2)->get_value());
    }else if (v1->is_expr()) {
        return to_expr(v1)->m_expr==to_expr(v2)->m_expr;
    }else if (v1->is_var_offset()) {
        if (to_var_offset(v1)->get_is_negated()==to_var_offset(v2)->get_is_negated()) {
            val * vo1 = to_var_offset(v1)->get_offset();
            val * vo2 = to_var_offset(v2)->get_offset();
            if (vo1 && vo2) {
                return is_eq(vo1, vo2);
            }
            //get the non-null one, if any
            vo1 = vo2 ? vo2 : vo1;
            if (vo1) {
                if (vo1->is_int()) {
                    return m_zm.is_zero(to_int(vo1)->get_value());
                }
                else {
                    SASSERT(false);
                }
            }else{
                return true;
            }
        }
        return false;
    }
    SASSERT(false);
    return false;
}

bool mc_context::is_eq(value_tuple * v1, value_tuple * v2) {
    SASSERT(v1->get_size()==v2->get_size());
    for( unsigned i=0; i<v1->get_size(); i++ ){
        if (!is_eq(v1->m_vec[i], v2->m_vec[i])) {
            return false;
        }
    }
    return true;
}

//are two abstract values equal
bool mc_context::is_eq(abs_val * a1, abs_val * a2) {
    if (a1->is_value()) {
        if (a2->is_value()) {
            return is_eq(to_value(a1)->get_value(), to_value(a2)->get_value());
        }
        else if (a2->is_interval()) {
            return is_eq(a2,a1);
        }
    }else if (a1->is_star()) {
        if (a2->is_star()) {
            return true;
        }
        else if (a2->is_interval()) {
            return is_eq(a2,a1);
        }
    }else if (a1->is_interval()) {
        for (unsigned i=0; i<2; i++) {
            val * b1 = i==0 ? to_interval(a1)->get_lower() : to_interval(a1)->get_upper();
            val * b2 = get_bound(a2, i==0);
            if (b1 && b2) {
                if (!is_eq(b1, b2)) {
                    return false;
                }
            }
            else if (b1 || b2) {
                return false;
            }
        }
        return true;
    }
    else {
        SASSERT(false);
    }
    return false;
}

//are two conditions equal
bool mc_context::is_eq(cond * c1, cond * c2) {
    SASSERT(c1->get_size()==c2->get_size());
    for( unsigned i=0; i<c1->get_size(); i++ ){
        if (!is_eq(c1->m_vec[i], c2->m_vec[i])) {
            return false;
        }
    }
    return true;
}

//are two condition compatible
bool mc_context::is_compatible(abs_val * a1, abs_val * a2) {
    if (a1->is_star()) {
        return true;
    }
    else if (a1->is_value()) {
        return is_generalization(a2, a1);
    }
    else if (a1->is_interval()) {
        val * nb[2] = { 0, 0 };
        for (unsigned i=0; i<2; i++) {
            val * b1 = i==0 ? to_interval(a1)->get_lower() : to_interval(a1)->get_upper();
            val * b2 = get_bound(a2, i==0);
            //take the upper bound of lower bounds, and lower bound of upper bounds, store in nb[0], nb[1]
            nb[i] = (is_lt(b1,b2,i==0) ? (i==0 ? b2 : b1) : (i==0 ? b1 : b2)); 
        }
        TRACE("mc_context_debug", tout << "Is compatible : ";
                                  display(tout,a1);
                                  tout << " ";
                                  display(tout,a2);
                                  tout << ", result = " << !nb[1] || !is_lt(nb[1],nb[0]);
                                  tout << "\n";);
        //their intersection is from nb[0]...nb[1]
        //compatible if either nb[1] is +INF, or nb[1] >= nb[0]
        return !nb[1] || !is_lt(nb[1],nb[0]);
    }
    return false;
}

//are two condition compatible
bool mc_context::is_compatible(cond * c1, cond * c2) {
    SASSERT(c1->get_size()==c2->get_size());
    for (unsigned i=0; i<c1->get_size(); i++) {
        if (!is_compatible(c1->get_value(i),c2->get_value(i))) {
            return false;
        }
    }
    return true;
}

//does a1 generalize a2
bool mc_context::is_generalization(abs_val * a1, abs_val * a2) {
    if (a1->is_star()) {
        return true;
    }
    else if (a1->is_value()) {
        return is_eq(a1, a2);
    }
    else if (a1->is_interval()) {
        for (unsigned i=0; i<2; i++) {
            val * b1 = i==0 ? to_interval(a1)->get_lower() : to_interval(a1)->get_upper();
            val * b2 = get_bound(a2, i==0);
            //b2 is less than/greater than b1
            if (is_lt(i==0 ? b2 : b1, i==0 ? b1 : b2, i==0)) {
                return false;
            }
        }
        TRACE("mc_context_debug", tout << "Generalization : ";
                                  display(tout,a1);
                                  tout << " ";
                                  display(tout,a2);
                                  tout << "\n";);
        return true;
    }
    return false;
}

//does c1 generalize c2
bool mc_context::is_generalization(cond * c1, cond * c2) {
    SASSERT(c1->get_size()==c2->get_size());
    for (unsigned i=0; i<c1->get_size(); i++) {
        if (!is_generalization(c1->get_value(i), c2->get_value(i))) {
            return false;
        }
    }
    return true;
}

bool mc_context::is_generalization(cond * c, ptr_buffer<val> & vals) {
    SASSERT(c->get_size()==vals.size());
    for (unsigned i=0; i<c->get_size(); i++) {
        if (!c->get_value(i)->is_star()) {
            if (c->get_value(i)->is_value() && !is_eq(to_value(c->get_value(i))->get_value(),vals[i])) {
                return false;
            }
        }
    }
    return true;
}

//do meet
abs_val * mc_context::mk_meet(abs_val * a1, abs_val * a2) {
    TRACE("mc_context_debug", tout << "mk_meet ";
                              display(tout, a1);
                              tout << " ";
                              display(tout, a2);
                              tout << "\n";);
    SASSERT(is_compatible(a1,a2));
    if (a1->is_star()) {
        return a2;
    }
    else if (a1->is_value()) {
        return a1;
    }
    else if (a1->is_interval()) {
        if (a2->is_interval()) {
            val * nb[2];
            for (unsigned i=0; i<2; i++) {
                val * b1 = get_bound(a1, i==0);
                val * b2 = get_bound(a2, i==0);
                //take the upper bound of the lowers, and the lower bound of the uppers
                nb[i] = (is_lt(b1,b2,i==0) ? (i==0 ? b2 : b1) : (i==0 ? b1 : b2)); 
            }
            //TODO: make only if it is different from both a1 and a2
            return mk_interval(nb[0], nb[1]);
        }
        else {
            return mk_meet(a2, a1);
        }
    }
    else {
        //unknown abstract value
        SASSERT(false);
        return 0;
    }
}

//do meet
cond * mc_context::mk_meet(cond * c1, cond * c2) {
    SASSERT(c1->get_size()==c2->get_size());
    SASSERT(is_compatible(c1,c2));
    cond * cm = copy(c1);
    for (unsigned i=0; i<c1->get_size(); i++) {
        cm->m_vec[i] = mk_meet(c1->get_value(i), c2->get_value(i));
    }
    return cm;
}

def * mc_context::mk_product(def * d1, def * d2) {
    def * d = new_def();
    for( unsigned i=0; i<d1->get_num_entries(); i++ ){
        cond * cc = d1->get_condition(i);
        if (cc->is_value()) {
            value_tuple * ve = d2->evaluate(*this, cc);
            if (ve) {
                value_tuple * vv = mk_concat(d1->get_value(i), ve);
                d->append_entry(*this, cc, vv);
            }
        }
        else {
            for( unsigned j=0; j<d2->get_num_entries(); j++ ){
                if (is_compatible(d1->get_condition(i), d2->get_condition(j))) {
                    cond * c = mk_meet(d1->get_condition(i), d2->get_condition(j));
                    value_tuple * v = mk_concat(d1->get_value(i), d2->get_value(j));
                    d->append_entry(*this, c, v);
                }
            }
        }
    }
    return d;
}

cond * mc_context::mk_compose(cond * c1, value_tuple * v, cond * c2) {
    SASSERT(v->get_size()==c2->get_size());
    //we first check if the compose will succeed before copying c1
    //store the values within c1 that change
    m_new_vals.reset();
    for( unsigned i=0; i<v->get_size(); i++ ){
        if( c2->m_vec[i]!=0 ){
            abs_val * curr = 0;
            abs_val * curr_tgt = c2->get_value(i);
            bool isVar = false;
            unsigned vid;
            val * vi = v->get_value(i);
            //check if v.i is a variable x_vid, if so will match c1.vid with c2.i
            if (vi->is_expr() && is_var(to_expr(vi)->get_value())) {
                isVar = true;
                vid = to_var(to_expr(vi)->get_value())->get_idx();
                if (!m_new_vals.find(vid,curr)) {
                    curr = c1->get_value(vid);
                }
            }
            else if (vi->is_var_offset()) {
                //similarly if it is variable offset
                isVar = true;
                vid = to_var_offset(vi)->get_variable()->get_idx();
                if (!m_new_vals.find(vid,curr)) {
                    curr = c1->get_value(vid);
                }
                //additionally, we must apply inverse of offset to the target
                val * vo = to_var_offset(vi)->get_offset();
                if (vo) {
                    vo = mk_negate(vo);
                    curr_tgt = mk_offset(curr_tgt, vo);
                }
                if (to_var_offset(vi)->get_is_negated()) {
                    curr_tgt = mk_negate(curr);
                }
            }
            else {   //otherwise match v.i with c2.i
                //must convert from value to abstract value
                curr = mk_value(vi);
            }
            //check if it is compatible
            if (is_compatible(curr, curr_tgt)) {
                if (isVar) {
                    m_new_vals.erase(vid);
                    m_new_vals.insert(vid, mk_meet(curr, curr_tgt));
                }
            }
            else {
                //compose has failed
                return 0;
            }
        }
    }
    //now, copy c1, taking indicies that changed
    if (m_new_vals.empty()) {
        return c1;
    }
    else {
        cond * cc = copy( c1 );
        for (unsigned i=0; i<c1->get_size(); i++) {
            if (!m_new_vals.find(i,cc->m_vec[i])) {
                cc->m_vec[i] = c1->m_vec[i];
            }
        }
        return cc;
    }
}

bool mc_context::do_compose(expr_ref_buffer & c1, expr_ref_buffer & v, expr_ref_buffer & e1, annot_entry * c2) {
    SASSERT(v.size()==c2->get_size());
    SASSERT(c1.size()==e1.size());
    SASSERT(c2->is_value());
    //do the compose
    for (unsigned j=0; j<v.size(); j++) {
        expr * c2v = c2->get_value(j);
        if (is_var(v[j])) {
            unsigned vid = to_var(v[j])->get_idx();
            if (c1[vid]) {
                if (c1[vid]!=c2v) {
                    return false;
                }
            }
            else {
                c1.set(vid, c2v);
                unsigned v_index = (c1.size()-1)-vid;
                expr * c2a = c2->get_annotation(j);
                if (!e1[v_index] || get_depth(e1[v_index])>get_depth(c2a)) {
                    //if (e1[v_index]) {
                    //    std::cout << "depth " << get_depth(e1[v_index]) << " " << get_depth(tc2->get_value(j)) << "\n";
                    //}
                    e1.set(v_index, c2a);
                }
            }
        }
        else if (v[j]!=c2v) {
            return false;
        }
    }
    return true;
}


def * mc_context::mk_var_relation(def * d, func_decl * f, var * v, bool is_flipped) {
    unsigned vid = v->get_idx();
    def * nd = new_def();
    for (unsigned i=0; i<d->get_num_entries(); i++) {
        //check the type of the abstract value
        abs_val * a = d->get_condition(i)->get_value(vid);
        val * vl = d->get_value(i)->get_value(0);
        TRACE("model_check_var_relation",tout << "mk var relation var : " << mk_pp(v,m_m) << ", abs val : "; display(tout, a); tout << ", value : "; display(tout, vl); tout << "\n";);
        //if the condition is star or value, we know it is pointwise projection
        //  thus, it must be the case of equality
        if (a->is_value()) {
            SASSERT(m_m.is_eq(f));
            //check if it is equal
            val * ret = mk_val(is_eq(to_value(a)->get_value(), vl) ? m_true : m_false);
            nd->append_entry(*this, d->get_condition(i), mk_value_tuple(ret));
        }
        else if (a->is_star()) {
            SASSERT(m_m.is_eq(f));
            // if it is * -> vl, then we add vl -> true, * -> false
            cond * c = cond::mk(*this, d->get_condition(i)->get_size());
            for (unsigned j=0; j<c->get_size(); j++) {
                c->m_vec[j] = j==vid ? mk_value(vl) : d->get_condition(i)->get_value(j);
            }
            val * ret = mk_val(m_true);
            nd->append_entry(*this, c, mk_value_tuple(ret));
            ret = mk_val(m_false);
            nd->append_entry(*this, d->get_condition(i), mk_value_tuple(ret));
        }
        else if (a->is_interval()) {
            //value should be an integer
            SASSERT(vl->is_int());
            ptr_vector<av_interval> interval_bounds;
            ptr_vector<val> rets;
            if (m_m.is_eq(f)) {
                for (unsigned j=0; j<2; j++) {
                    mpz b(j==0 ? -1 : 1);
                    m_zm.add(b, to_int(vl)->get_value(), b);
                    val * bval = mk_val(b);
                    interval_bounds.push_back(mk_interval(j==0 ? 0 : bval, j==0 ? bval : 0));
                    rets.push_back(mk_val(m_false));
                }
                interval_bounds.push_back(mk_interval(vl, vl));
                rets.push_back(mk_val(m_true));
            }
            else {
                //split x into 2 bounds
                // for >   (-INF, v] -> false, [v+1, INF) -> true
                // for >=  (-INF, v-1] -> false, [v, INF) -> true
                // for <   (-INF, v-1] -> true, [v, INF) -> false
                // for <=  (-INF, v] -> true, [v+1, INF) -> false
                ptr_vector<val> bounds;
                bool isStrict = f->get_decl_kind()==OP_LT || f->get_decl_kind()==OP_GT;
                bool isGreater = (f->get_decl_kind()==OP_LE || f->get_decl_kind()==OP_LT)==is_flipped;
                for (unsigned j=0; j<2; j++) {
                    val * bval = vl;
                    if ((j==1)==(isStrict==isGreater)) {
                        mpz b(j==1 ? 1 : -1);
                        m_zm.add(b, to_int(vl)->get_value(), b);
                        bval = mk_val(b);
                    }
                    interval_bounds.push_back(mk_interval(j==0 ? 0 : bval, j==0 ? bval : 0));
                    rets.push_back(mk_val((j==1)==isGreater ? m_true : m_false));
                }
            }
            TRACE("model_check_var_relation",tout << "Split relation " << mk_pp(f,m_m) << (is_flipped ? " (flipped)" : "") << " for value "; display(tout, vl); tout << " into : \n";
                                             for (unsigned j=0; j<interval_bounds.size(); j++) {
                                                tout << "   ";
                                                display(tout, interval_bounds[j]);
                                                tout << " -> ";
                                                display(tout, rets[j]);
                                                tout << "\n";
                                             });
                
            //now process the intervals
            for (unsigned j=0; j<interval_bounds.size(); j++) {
                if (is_compatible(a, interval_bounds[j])) {
                    abs_val * avm = mk_meet(a, interval_bounds[j]);
                    cond * c = cond::mk(*this, d->get_condition(i)->get_size());
                    for (unsigned k=0; k<c->get_size(); k++) {
                        c->m_vec[k] = k==vid ? avm : d->get_condition(i)->get_value(k);
                    }
                    TRACE("model_check_var_relation", tout << "Add condition "; display(tout, c, rets[j]); tout << "\n";);
                    nd->append_entry(*this, c, mk_value_tuple(rets[j]));
                }
            }
        }
    }
    return nd;
}

def * mc_context::mk_var_offset(def * d, var * v, bool is_negated) {
    unsigned vid = v->get_idx();
    def * nd = new_def();
    for (unsigned i=0; i<d->get_num_entries(); i++) {
        val * vl = d->get_value(i)->get_value(0);
        val * vovl = mk_val(v, vl, is_negated);
        nd->append_entry(*this, d->get_condition(i), mk_value_tuple(vovl));
    }
    return nd;
}

def * mc_context::mk_compose(def * df, def * da) {
    def * d = new_def();
    for (unsigned i=0; i<da->get_num_entries(); i++) {
        //bool end_early = false;
        for (unsigned j=0; j<df->get_num_entries(); j++) {
            cond * cc = mk_compose(da->get_condition(i), da->get_value(i), df->get_condition(j));
            if( cc!=0 ){
                if (d->append_entry(*this, cc, df->get_value(j))) {
                    //SASSERT(!end_early);
                }
                if (cc==da->get_condition(i)) {
                    //end_early = true;
                    break;
                }
            }
        }
        
    }
    return d;
}

bool mc_context::do_compose(func_decl * f, def * d) {
    SASSERT(!is_uninterp(f));
    ptr_buffer<value_tuple> computed_vals;
    //interpreted case
    for( unsigned i=0; i<d->get_num_entries(); i++ ){
        value_tuple * v = d->get_value(i);
        ptr_buffer<val> vals;
        for (unsigned j=0; j<v->get_size(); j++) {
            vals.push_back(v->get_value(j));
        }
        //evaluate to create the new value
        val * ve = evaluate_interp(f, vals);
        if (!ve) return false;
        computed_vals.push_back(mk_value_tuple(ve));
    }
    d->m_values.reset();
    d->m_values.append(computed_vals.size(), computed_vals.c_ptr());
    //d->has_simplified = false;
    return true;
}

av_star * mc_context::mk_star() {
    if (!m_star) {
        void * mem = allocate(sizeof(av_star));
        m_star = new (mem) av_star();
    }
    return m_star;
}

av_val * mc_context::mk_value(val * v) {
    //FIXME: should we cache like this?
    av_val * a;
    if (m_val_to_abs_val.find(v, a)) {
        return a;
    }
    else {
        void * mem = allocate(sizeof(av_val));
        a = new (mem) av_val(v);
        m_val_to_abs_val.insert(v, a);
        return a;
    }
}

av_interval * mc_context::mk_interval(val * l, val * u) {
    //TODO: cache?
    // either l is -INF, or u >= l
    SASSERT(!l || !u || (l->is_int() && u->is_int()) || (l->is_bv() && u->is_bv()));
    void * mem = allocate(sizeof(av_interval));
    av_interval * av = new (mem) av_interval(l, u);
    TRACE("mc_context_debug", tout << "mk_interval ";
                              display(tout,av);
                              tout << "\n";);
    SASSERT(!l || !is_lt(u,l,false));
    return av;
}

av_interval * mc_context::mk_next_interval(val * l, val * u) {
    val * ll = l;
    if (ll) {
        if (l->is_int()) {
            mpz curr(1);
            m_zm.add(curr,to_int(l)->get_value(),curr);
            ll = mk_val(curr);
        }
        else if (l->is_bv()) {
            mpz curr(1);
            m_zm.add(curr,to_bv(l)->get_value(),curr);
            ll = mk_val(curr, to_bv(l)->get_size());
        }
        else {
            SASSERT(false);
        }
    }
    return mk_interval(ll, u);
}

cond * mc_context::mk_star(unsigned sz) {
    cond * cstar;
    if (!m_size_to_star.find(sz,cstar)) {
        cstar = cond::mk(*this, sz);
        for (unsigned i=0; i<sz; i++) {
            cstar->m_vec[i] = mk_star();
        }
        m_size_to_star.insert(sz,cstar);
    }
    return cstar;
}

cond * mc_context::mk_star(model_constructor * mct, quantifier * q) {
    cond * cstar;
    if (!m_quant_to_cond_star.find(q,cstar)) {
        cstar = cond::mk(*this, q->get_num_decls());
        for (unsigned i=0; i<cstar->get_size(); i++) {
            cstar->m_vec[i] = mct->get_projection(*this, q, i)->get_projected_default(*this);
        }
        m_quant_to_cond_star.insert(q, cstar);
    }
    return cstar;
}

cond * mc_context::mk_cond(ptr_buffer<abs_val> & avals) {
    cond * c = cond::mk(*this,avals.size());
    for (unsigned i=0; i<c->get_size(); i++) {
        c->m_vec[i] = avals[i];
    }
    return c;
}

cond * mc_context::mk_cond(ptr_buffer<val> & vals) {
    ptr_buffer<abs_val> avals;
    for (unsigned k=0; k<vals.size(); k++) {
        avals.push_back(mk_value(vals[k]));
    }
    return mk_cond(avals);
}

cond * mc_context::mk_cond(annot_entry * tc) {
    ptr_buffer<val> vals;
    for (unsigned i=0; i<tc->get_size(); i++) {
        vals.push_back(mk_val(tc->get_value(i)));
    }
    return mk_cond(vals);
}

cond * mc_context::copy(cond * c) {
    cond * cc = cond::mk(*this, c->get_size());
    for (unsigned i=0; i<c->get_size(); i++) {
        cc->m_vec[i] = c->m_vec[i];
    }
    return cc;
}

annot_entry * mc_context::mk_annot_entry(expr_ref_buffer & values, expr_ref_buffer & annotations, expr * result) {
    SASSERT(values.size()==annotations.size());
    annot_entry * tc = annot_entry::mk(*this, values.size());
    for (unsigned i=0; i<tc->get_size(); i++) {
        tc->m_vec[i] = values[i];
        tc->m_vec[values.size()+i] = annotations[i];
    }
    tc->m_result = result;
    return tc;
}

annot_entry * mc_context::mk_annot_entry(ptr_buffer<expr> & values, ptr_buffer<expr> & annotations, expr * result) {
    SASSERT(values.size()==annotations.size());
    annot_entry * tc = annot_entry::mk(*this, values.size());
    for (unsigned i=0; i<tc->get_size(); i++) {
        tc->m_vec[i] = values[i];
        tc->m_vec[values.size()+i] = annotations[i];
    }
    tc->m_result = result;
    return tc;
}

annot_entry * mc_context::mk_annot_entry(expr_ref_buffer & values, expr * annotate_t, expr * result) {
    SASSERT(is_app(annotate_t));
    SASSERT(values.size()==to_app(annotate_t)->get_num_args());
    annot_entry * tc = annot_entry::mk(*this, values.size());
    for (unsigned i=0; i<tc->get_size(); i++) {
        tc->m_vec[i] = values[i];
        tc->m_vec[values.size()+i] = to_app(annotate_t)->get_arg(i);
    }
    tc->m_result = result;
    return tc;
}

def * mc_context::new_def() {
    void * mem = allocate(sizeof(def));
    return new (mem) def;
}

simple_def * mc_context::new_simple_def() {
    void * mem = allocate(sizeof(simple_def));
    return new (mem) simple_def;
}

val * mc_context::mk_canon(val * v) {
    TRACE("mk_canon_debug", tout << "Canonizing "; display(tout,v); tout << "\n";);
    expr_ref e(m_m);
    get_expr_from_val(v, e);
    //expressions use perfect caching, values are mapped to expr, so this is canonical
    val * vn = mk_val(e);
    SASSERT(is_eq(v,vn));
    return vn;
}

value_tuple * mc_context::mk_canon(value_tuple * vt) {
    ptr_vector<val> vals;
    bool changed = false;
    for (unsigned i=0; i<vt->get_size(); i++) {
        val * vv = mk_canon(vt->get_value(i));
        vals.push_back(vv);
        changed = changed || vv!=vt->get_value(i);
    }
    if (changed) {
        value_tuple * vtn = value_tuple::mk(*this, vt->get_size());
        for (unsigned i=0; i<vtn->get_size(); i++) {
            vtn->m_vec[i] = vals[i];
        }
        return vtn;
    }
    else {
        return vt;
    }
}

abs_val * mc_context::mk_canon(abs_val * a) {
    if (a->is_value()) {
        return mk_value(mk_canon(to_value(a)->get_value()));
    }
    else if (a->is_interval()) {
        bool changed = false;
        val * vn[2];
        for (unsigned i=0; i<2; i++) {
            val * v = i==0 ? to_interval(a)->get_lower() : to_interval(a)->get_upper();
            vn[i] = v ? mk_canon(v) : v;
            changed = changed || vn[i]!=v;
        }
        if (changed) {
            return mk_interval(vn[0], vn[1]);
        }
    }
    return a;
}

cond * mc_context::mk_canon(cond * c) {
    ptr_vector<abs_val> vals;
    bool changed = false;
    for (unsigned i=0; i<c->get_size(); i++) {
        abs_val * avv = mk_canon(c->get_value(i));
        vals.push_back(avv);
        changed = changed || avv!=c->get_value(i);
    }
    if (changed) {
        cond * cn = cond::mk(*this, c->get_size());
        for (unsigned i=0; i<cn->get_size(); i++) {
            cn->m_vec[i] = vals[i];
        }
        return cn;
    }
    else {
        return c;
    }
}

void mc_context::get_expr_from_val(val * v, expr_ref & e) {
    if (v->m_expr) {
        e = v->m_expr;
    }
    else {
        if (v->is_int()) {
            rational r(to_int(v)->get_value());
            e = m_au.mk_numeral(r, true);
        }
        else if (v->is_bv()) {
            rational r(to_bv(v)->get_value());
            e = m_bvu.mk_numeral(r, to_bv(v)->get_size());
        }
        else {
            SASSERT(false);
        }
    }
}

expr * mc_context::mk_distinguished_constant_expr(sort * s) {
    if (!m_sort_to_dist_expr.contains(s)) {
        expr_ref edc(m_m);
        edc = m_m.mk_fresh_const(0,s);
        //should be memory managed
        m_expr_produced_global.push_back(edc);
        m_sort_to_dist_expr.insert(s, edc);
        return edc;
    }
    return m_sort_to_dist_expr.find(s);
}

//make some value
expr * mc_context::get_some_value(sort * s) { 
    expr_ref edc(m_m);
    edc = m_m.get_some_value(s); 
    m_expr_produced_global.push_back(edc);
    return edc;
}

expr * mc_context::mk_simple_add(expr * e, int o) {
    rational r;
    if (m_au.is_numeral(e, r)) {
        mpz result(o);
        m_zm.add(r.to_mpq().numerator(), result, result);
        expr * v = m_au.mk_numeral(result, true);
        if (!m_expr_produced.contains(v)) {
            m_expr_produced.push_back(v);
        }
        return v;
    }
    else {
        SASSERT(false);
        return 0;
    }
}

void mc_context::mk_offset_sub(expr * e, expr * o, expr_ref & r) {
    sort * s = get_sort(e);
    if (m_au.is_int(s)) {
        expr * on;
        rational rat;
        if (m_au.is_numeral(o, rat)) {
            mpz neg_one(-1);
            mpz result;
            m_zm.mul(neg_one,rat.to_mpq().numerator(),result);
            on = m_au.mk_numeral(rational(result), true);
        }
        else {
            on = m_au.mk_mul(m_au.mk_numeral(rational(-1), true),o);
        }
        r = m_au.mk_add(e, on);
    }
    else if (m_bvu.is_bv_sort(s)) {
        expr * on;
        rational rat;
        unsigned sz = m_bvu.get_bv_size(s);
        if (m_bvu.is_numeral(o, rat, sz)) {
            mpz neg_one(-1);
            mpz result;
            m_zm.mul(neg_one,rat.to_mpq().numerator(),result);
            on = m_bvu.mk_numeral(rational(result), sz);
        }
        else {
            on = m_bvu.mk_bv_mul(m_bvu.mk_numeral(rational(-1),sz),o);
        }
        r = m_bvu.mk_bv_add(e, on);
    }
    else {
        SASSERT(false);
    }
}

void mc_context::display(std::ostream & out, expr * e) {
    out << mk_pp(e,m_m);
}

//display the value
void mc_context::display(std::ostream & out, val * v) {
    if (v->is_int()) {
        m_zm.display(out, to_int(v)->get_value());
    }
    else if (v->is_bv()) {
        out << "BV[" << to_bv(v)->get_size() << "]( ";
        m_zm.display(out, to_bv(v)->get_value());
        out << " )";
    }
    else if (v->is_expr()) {
        display(out, to_expr(v)->get_value());
    }
    else if (v->is_var_offset()) {
        out << ( to_var_offset(v)->get_is_negated() ? "- " : "");
        display(out,to_var_offset(v)->get_variable());
        val * off = to_var_offset(v)->get_offset();
        if (off) {
            out << " + ";
            display(out, off);
        }
    }
}

//display the abstract value
void mc_context::display(std::ostream & out, abs_val * av) {
    if (av->is_value()) {
        display(out,to_value(av)->get_value());
    }
    else if (av->is_interval()) {
        out << "[ ";
        if (to_interval(av)->get_lower()) {
            display(out, to_interval(av)->get_lower());
        }
        else {
            out << "-INF";
        }
        out << ", ";
        if (to_interval(av)->get_upper()) {
            display(out, to_interval(av)->get_upper());
        }
        else {
            out << "INF";
        }
        out << " ]";
    }
    else if (av->is_star()) {
        out << "*";
    }
}

//display the tuple of values
void mc_context::display(std::ostream & out, value_tuple * vt) {
    out << "(";
    for( unsigned i=0; i<vt->get_size(); i++ ){
        if(i>0) out << ", ";
        display(out, vt->m_vec[i]);
    }
    out << ")";
}

//display the condition (tuple of abstract values)
void mc_context::display(std::ostream & out, cond * c) {
    out << "(";
    for( unsigned i=0; i<c->get_size(); i++ ){
        if(i>0) out << ", ";
        display(out, c->get_value(i));
    }
    out << ")";
}

void mc_context::display(std::ostream & out, cond * c, val * v) {
    display(out, c);
    out << " -> ";
    display(out, v);
}

void mc_context::display(std::ostream & out, cond * c, value_tuple * vt) {
    display(out, c);
    out << " -> ";
    display(out, vt);
}

void mc_context::display(std::ostream & out, annot_entry * tc) {
    out << "(";
    for( unsigned i=0; i<tc->get_size(); i++ ){
        if(i>0) out << ", ";
        display(out, tc->get_value(i));
    }
    out << ")";
    out << " -> ";
    display(out, tc->get_result());
    out << "   annotation : (";
    for( unsigned i=0; i<tc->get_size(); i++ ){
        if(i>0) out << ", ";
        display(out, tc->get_annotation(i));
    }
    out << ")";
}

//display the definition
void mc_context::display(std::ostream & out, def * d) {
    for( unsigned i=0; i<d->get_num_entries(); i++ ){
        display(out, d->get_condition(i), d->get_value(i));
        out << "\n";
    }
}

void mc_context::display(std::ostream & out, simple_def * d) {
    for( unsigned i=0; i<d->get_num_entries(); i++ ){
        display(out, d->get_condition(i));
        out << "\n";
    }
    if (d->get_else()) {
        out << "else -> ";
        display(out, d->get_else());
        out << "\n";
    }
}

val * mc_context::evaluate_interp(func_decl * f, ptr_buffer<val> & vals) {
    SASSERT(!is_uninterp(f));
    TRACE("evaluate_debug", tout << "evaluate " << mk_pp(f,m_m) << " with arguments: \n";
                            for (unsigned i=0; i<vals.size(); i++) {
                                display(tout, vals[i]);
                                tout << "\n";
                            });
    if (f->get_family_id()==m_au.get_family_id()) {
        for (unsigned i=0; i<vals.size(); i++) {
            SASSERT(vals[i]->is_int());
        }
        switch (f->get_decl_kind()) {
        case OP_LE:
            return mk_val(m_zm.le(to_int(vals[0])->get_value(),to_int(vals[1])->get_value()) ? m_true : m_false);
            break;
        case OP_GE:
            return mk_val(m_zm.ge(to_int(vals[0])->get_value(),to_int(vals[1])->get_value()) ? m_true : m_false);
            break;
        case OP_LT:
            return mk_val(m_zm.lt(to_int(vals[0])->get_value(),to_int(vals[1])->get_value()) ? m_true : m_false);
            break;
        case OP_GT:
            return mk_val(m_zm.gt(to_int(vals[0])->get_value(),to_int(vals[1])->get_value()) ? m_true : m_false);
            break;
        case OP_ADD:
            {
                mpz curr(0);
                for (unsigned i=0; i<vals.size(); i++) {
                    m_zm.add(curr,to_int(vals[i])->get_value(),curr);
                }
                return mk_val(curr);
            }
            break;
        case OP_MUL:
            {
                mpz curr(1);
                for (unsigned i=0; i<vals.size(); i++) {
                    m_zm.mul(curr,to_int(vals[i])->get_value(),curr);
                }
                return mk_val(curr);
            }
            break;
        case OP_REM:
            {
                if (m_zm.is_zero(to_int(vals[1])->get_value())) {
                    return 0;
                }
                else {
                    mpz ret;
                    m_zm.rem(to_int(vals[0])->get_value(), to_int(vals[1])->get_value(), ret);
                    return mk_val(ret);
                }
            }
            break;
        case OP_DIV:
            {
                if (m_zm.is_zero(to_int(vals[1])->get_value())) {
                    return 0;
                }
                else {
                    mpz ret;
                    m_zm.div(to_int(vals[0])->get_value(), to_int(vals[1])->get_value(), ret);
                    return mk_val(ret);
                }
            }
            break;
        case OP_MOD:
            {
                if (m_zm.is_zero(to_int(vals[1])->get_value())) {
                    return 0;
                }
                else {
                    mpz ret;
                    m_zm.mod(to_int(vals[0])->get_value(), to_int(vals[1])->get_value(), ret);
                    return mk_val(ret);
                }
            }
            break;
        }

    }
    else if (f->get_family_id()==m_bvu.get_family_id()) {

    }
    else if (m_m.is_eq(f)) {
        return mk_val(is_eq(vals[0], vals[1]) ? m_true : m_false);
    }
    else if (f->get_family_id()==m_m.get_basic_family_id() && f->get_decl_kind()==OP_ITE) {
        return m_m.is_true(to_expr(vals[0])->get_value()) ? vals[1] : vals[2];
    }
    //default case
    expr_ref_buffer evals(m_m);
    for (unsigned i=0; i<vals.size(); i++) {
        expr_ref v(m_m);
        get_expr_from_val(vals[i], v);
        evals.push_back(v);
    }
    expr * e = evaluate_interp(f, evals);
    if (e) {
        return mk_val(e);
    }
    SASSERT(false);
    return 0;
}

expr * mc_context::evaluate_interp(func_decl * f, expr_ref_buffer & vals) {
    SASSERT(!is_uninterp(f));
    TRACE("evaluate_debug", tout << "evaluate " << mk_pp(f,m_m) << " with arguments: \n";
                            for (unsigned i=0; i<vals.size(); i++) {
                                display(tout, vals[i]);
                                tout << "\n";
                            });
    if (!m_m.is_eq(f)) {
        for (unsigned i=0; i<vals.size(); i++) {
            if (i==0 || !m_m.is_ite(f)) {
                SASSERT(is_atomic_value(vals[i]));
            }
        }
    }
    if (f->get_family_id()==m_au.get_family_id()) {
        if (f->get_decl_kind()==OP_REM || f->get_decl_kind()==OP_DIV || f->get_decl_kind()==OP_MOD) {
            rational r;
            if (m_au.is_numeral(vals[1], r)) {
                if (m_zm.is_zero(r.to_mpq().numerator())) {
                    return 0;
                }
            }
            else {
                SASSERT(false);
            }
        }
        //use rewriter
        expr_ref nr(m_m);
        m_ar.mk_app(f, vals.size(), vals.c_ptr(), nr);
        if (!m_expr_produced.contains(nr)) {
            m_expr_produced.push_back(nr);
        }
        return nr;
    }
    else if (f->get_family_id()==m_bvu.get_family_id()) {
        //use rewriter
        expr_ref nr(m_m);
        m_bvr.mk_app(f, vals.size(), vals.c_ptr(), nr);
        if (!m_expr_produced.contains(nr)) {
            m_expr_produced.push_back(nr);
        }
        return nr;
    }
    else if (m_m.is_eq(f)) {
        return vals[0]==vals[1] ? m_true : m_false;
    }
    else if (f->get_family_id()==m_m.get_basic_family_id()) {
        switch (f->get_decl_kind()) {
        case OP_AND:
            for (unsigned i=0; i<vals.size(); i++) {
                if (m_m.is_false(vals[i])) {
                    return m_false;
                }
            }
            return m_true;
            break;
        case OP_OR:
            for (unsigned i=0; i<vals.size(); i++) {
                if (m_m.is_true(vals[i])) {
                    return m_true;
                }
            }
            return m_false;
            break;
        case OP_IFF:
            return vals[0]==vals[1] ? m_true : m_false;
            break;
        case OP_NOT:
             return m_m.is_true(vals[0]) ? m_false : m_true;
            break;
        case OP_ITE:
            return m_m.is_true(vals[0]) ? vals[1] : vals[2];
            break;
        }
    }
    TRACE("evaluate_warn", tout << "Don't know how to evaluate " << mk_pp(f,m_m) << "\n";);
    SASSERT(false);
    return 0;
}


//evaluate ground term 
expr * mc_context::evaluate(model_constructor * mct, expr * e, expr_ref_buffer & vsub, bool partial) {
    if (is_atomic_value(e)) {
        return e;
    }
    else if (is_app(e)) {
        expr * ev = 0;
        if (is_ground(e)) {
            if (partial && m_ground_partial_evaluations.find(e, ev)) {
                return ev;
            }
            else if (!partial && m_ground_evaluations.find(e, ev)) {
                return ev;
            }
        }
        else if (m_evaluation_cache_active) {
            if (partial && m_partial_evaluations.find(e, ev)) {
                return ev;
            }
            else if (!partial && m_evaluations.find(e, ev)) {
                return ev;
            }
        }
        /*
        static int grCount = 0;
        static int ngrCount = 0;
        if (is_ground(e)) {
            grCount++;
        }
        else {
            ngrCount++;
            if (ngrCount%10000==0) {
                std::cout << "Ground/non-ground : " << grCount << " " << ngrCount << std::endl;
            }
        }
        */

        expr_ref_buffer children(m_m);
        bool children_valid = true;
        for (unsigned i=0; i<to_app(e)->get_num_args(); i++) {
            expr * vc = evaluate(mct, to_app(e)->get_arg(i), vsub, partial);
            if (!vc) {
                children_valid = false;
            }
            else {
                children.push_back(vc);
                //for short circuiting
                if (m_m.is_or(e) && m_m.is_true(vc)) {
                    ev = m_true;
                    break;
                }
                if (m_m.is_and(e) && m_m.is_false(vc)) {
                    ev = m_false;
                    break;
                }
            }
        }
        if (!ev && children_valid) {
            TRACE("eval_term_op", tout << "Evaluated children.\n";);
            func_decl * f = to_app(e)->get_decl();
            if (is_uninterp(e)) {
                simple_def * df  = mct->get_simple_def(*this, f);
                TRACE("eval_term_op", tout << "Evaluate uf.\n";);
                ev = df->evaluate(children, partial);
            }
            else {
                TRACE("eval_term_interp", tout << "Evaluate interpreted " << mk_pp(e,m_m) << "\n";);
                ev = evaluate_interp(f, children);
            }
        }
        TRACE("eval_term_debug", tout << (partial ? "(partial)" : "") << " evaluated " << mk_pp(e,m_m) << " to "; 
                                    if (ev==0) {tout << "[null]"; }else{ display(tout, ev); }
                                    tout << "\n";);
        if (is_ground(e)) {
            if (partial) {
                m_ground_partial_evaluations.insert(e, ev);
            }
            if (!partial || ev) {
                m_ground_evaluations.insert(e, ev);
            }
        }
        else if (m_evaluation_cache_active) {
            if (partial) {
                m_partial_evaluations.insert(e, ev);
            }
            if (!partial || ev) {
                m_evaluations.insert(e, ev);
            }
        }
        return ev;
    }
    else if (is_var(e)) {
        return vsub[to_var(e)->get_idx()];
    }
    else {
        SASSERT(false);
        return 0;
    }
}


expr * mc_context::evaluate(model_constructor * mct, expr * e, bool partial) {
    expr_ref_buffer vsub(m_m);
    return evaluate(mct, e, vsub, partial);
}

bool mc_context::add_instantiation(model_constructor * mct, quantifier * q, expr_ref_buffer & vsub, expr_ref_buffer & instantiations,
                                   bool filterEval, bool filterRepair, bool filterCache) {
    //get the corresponding instantiation from the model construction object
    expr_ref_buffer inst(m_m);
    bool inst_found_expr;
    mct->get_inst(*this, q, vsub, inst, inst_found_expr);
    if (!inst_found_expr) {
    TRACE("inst_warn",tout << "Instantiate " << mk_pp(q,m_m) << " with \n";
                    for (unsigned j=0; j<inst.size(); j++) {
                            tout << "   " << mk_pp(inst[j],m_m) << "\n";
                    }
                    tout << "\n";
                    //tout << "Filters : " << filterEval << " " << filterRepair << " " << filterCache << "\n";
                    );
        TRACE("inst_warn", tout << "WARNING : did not find expressions in relevant domain.\n";);
    }
    for (unsigned j=0; j<inst.size(); j++) {
        if (!m_expr_produced_global.contains(inst[j])) {
            m_expr_produced_global.push_back(inst[j]);
        }
    }
    return add_instantiation(mct, q, inst, vsub, instantiations, filterEval, filterRepair, filterCache);
}

bool mc_context::add_instantiation(model_constructor * mct, quantifier * q, cond * c, expr_ref_buffer & instantiations,
                                  bool filterEval, bool filterRepair, bool filterCache) {
    //since condition may contain values made from direct evaluation, we must canonize the condition before consulting externally
    cond * cic = mk_canon(c);
    //get the corresponding instantiation from the model construction object
    expr_ref_buffer inst(m_m);
    bool inst_found_expr;
    mct->get_inst(*this, q, cic, inst, inst_found_expr);
    if (!inst_found_expr) {
    TRACE("inst_warn",tout << "Instantiate " << mk_pp(q,m_m) << " with \n";
                    for (unsigned j=0; j<inst.size(); j++) {
                            tout << "   " << mk_pp(inst[j],m_m) << "\n";
                    }
                    tout << "\n";
                    //tout << "Filters : " << filterEval << " " << filterRepair << " " << filterCache << "\n";
                    );
        TRACE("inst_warn", tout << "WARNING : did not find expressions in relevant domain.\n";);
    }
    for (unsigned j=0; j<inst.size(); j++) {
        if (!m_expr_produced_global.contains(inst[j])) {
            m_expr_produced_global.push_back(inst[j]);
        }
    }
    expr_ref_buffer val_subs(m_m);
    if (filterEval || filterRepair) {
        for (unsigned j=0; j<inst.size(); j++) {
            if (cic->get_value(j)->is_value()) {
                expr_ref ve(m_m);
                get_expr_from_val(to_value(cic->get_value(j))->get_value(), ve);
                val_subs.push_back(ve);
            }
            else {
                //evaluate to get value of term
                expr * ve = evaluate(mct, inst[(inst.size()-1)-j]);
                if (!ve) {
                    val_subs.reset();
                    break;
                }
                val_subs.push_back(ve);
            }
        }
    }
    return add_instantiation(mct, q, inst, val_subs, instantiations, filterEval, filterRepair, filterCache);
}
/*
bool mc_context::add_instantiation2(model_constructor * mct, quantifier * q, expr_ref_buffer & inst, expr_ref_buffer & vsub, expr_ref_buffer & instantiations,
                        bool filterEval, bool filterRepair, bool filterCache) {
    expr_ref_buffer inst2(m_m);
    bool inst_found_expr;
    mct->get_inst(*this, q, vsub, inst2, inst_found_expr);
    if (inst_found_expr) {
        for (unsigned i=0; i<inst2.size(); i++) {
            inst.set(i, inst2[i]);
        }
    }
    return add_instantiation(mct, q, inst, vsub, instantiations, filterEval, filterRepair, filterCache);
}
*/
bool mc_context::add_instantiation(model_constructor * mct, quantifier * q, expr_ref_buffer & inst, expr_ref_buffer & vsub, 
                                   expr_ref_buffer & instantiations,
                                   bool filterEval, bool filterRepair, bool filterCache) {
    SASSERT(inst.size()==q->get_num_decls());
    TRACE("inst_debug",tout << "Instantiate " << mk_pp(q,m_m) << " with \n";
                    for (unsigned j=0; j<inst.size(); j++) {
                            tout << "   " << mk_pp(inst[j],m_m);
                            if (!vsub.empty()) {
                                tout << ", value : " << mk_pp(vsub[(q->get_num_decls()-1)-j],m_m);
                            }
                            tout << "\n";
                    }
                    tout << "\n";
                    //tout << "Filters : " << filterEval << " " << filterRepair << " " << filterCache << "\n";
                    );

#ifdef MODEL_CHECK_DEBUG
    //make sure the terms evaluate to the right values
    for (unsigned j=0; j<vsub.size(); j++) {
        SASSERT(inst[j]);
        expr * ve = evaluate(mct, inst[j]);
        if (ve!=vsub[(vsub.size()-1)-j]) {
            TRACE("inst_warn",  tout << "Instantiate quantifier " << mk_pp(q,m_m) << " with : \n";
                                for( unsigned k=0; k<vsub.size(); k++) {
                                    tout << "   " << mk_pp(inst[(vsub.size()-1)-k],m_m) << " : ";
                                    display(tout, vsub[k]);
                                    tout << "\n";
                                }
                                tout << "ERROR:  not equal : ";
                                tout << mk_pp(inst[j],m_m) << ", value = ";
                                display(tout, ve);
                                tout << " and ";
                                display(tout, vsub[(vsub.size()-1)-j]);
                                tout << "\n";);
            SASSERT(false);
        }
    }
#endif
    //if (!inst_found_expr) std::cout << "    *** did not find expressions in relevant domain.\n";
    bool addInstantiation = true;
    //evaluate arguments, evaluate body directly
    if (filterEval || filterRepair) {
        if (vsub.size()==inst.size()) {
            if (filterEval && !filterRepair) {
                TRACE("inst_debug",tout << "Filter based on evaluation...\n";);
                expr * v = evaluate(mct, q->get_expr(), vsub);
                if (v && m_m.is_true(v)) {
                    TRACE("inst_debug",tout << "...instantiation evaluated to true in model.\n";);
                    addInstantiation = false;
                }
            }
            if (addInstantiation && filterRepair) {
                set_evaluate_cache_active(true);
                TRACE("inst_debug",tout << "Filter based on model repairing...\n";);
                if (mct->get_model_repair()->repair_formula(*this, mct, q, vsub, inst, instantiations)) {
                    TRACE("inst_debug",tout << "...instantiation was repaired.\n";);
                    addInstantiation = false;
                }
                set_evaluate_cache_active(false);
            }
        }
    }
    if (addInstantiation) {
        if (filterCache) {
            TRACE("inst_debug",tout << "Filter based on cache...\n";);
            inst_trie * it;
            if (!m_inst_trie.find(q, it)) {
                void * mem = allocate(sizeof(inst_trie));
                it = new (mem) inst_trie;
                m_inst_trie.insert(q,it);
            }
            if (!it->add(*this, inst)) {
                addInstantiation = false;
                TRACE("inst_debug",tout << "...instantiation was already added to cache.\n";);
            }
        }
        if (addInstantiation) {
            TRACE("inst",tout << "Instantiate " << mk_pp(q,m_m) << " with \n";
                            for (unsigned j=0; j<inst.size(); j++) {
                                    tout << "   " << mk_pp(inst[j],m_m) << "\n";
                            }
                            tout << "\n";
                            );
            expr_ref instance(m_m);
            instantiate(m_m, q, inst.c_ptr(), instance);
            instantiations.push_back(instance);
            return true;
        }
    }
    return false;
}
