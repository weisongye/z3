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

#define MODEL_CHECK_DEBUG

using namespace qsolver;

value_tuple * value_tuple::mk(mc_context & mc, unsigned arity) {
    //small_object_allocator & allocator = _m.get_allocator();
    void * mem = mc.allocate(sizeof(value_tuple) + arity * sizeof(val*) );
    return new (mem) value_tuple( arity );
}

cond * cond::mk(mc_context & mc, unsigned arity) {
    //small_object_allocator & allocator = _m.get_allocator();
    void * mem  = mc.allocate(sizeof(value_tuple) + arity * sizeof(abs_val*) );
    return new (mem) cond( arity );
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

bool cond_generalization_trie::add(mc_context & mc, cond * c, unsigned index, abs_val * star) {
    SASSERT(index<c->get_size());
    abs_val * curr = c->get_value(index);
    cond_generalization_trie * ct;
    //first check if it is generalized
    if (star!=curr && m_children.find(star,ct)) {
        if (index==(c->get_size()-1) || ct->has_generalization(mc, c, index+1, star)) {
            return false;
        }
    }
    if (m_children.find(curr, ct)) {
        if (index==(c->get_size()-1)) {
            // it's already there
            return false;
        }
        else {
            return ct->add(mc, c, index+1, star);
        }
    }
    else {
        if (index==(c->get_size()-1)) {
            //add dummy pointer
            m_children.insert(curr, 0);
        }
        else {
            void * mem = mc.allocate(sizeof(cond_generalization_trie));
            ct = new (mem) cond_generalization_trie;
            m_children.insert(curr, ct);
            ct->add(mc, c, index+1, star);
        }
        return true;
    }
}

bool cond_generalization_trie::add(mc_context & mc, cond * c) { 
    if (c->get_size()==0) {
        if (m_children.empty()) {
            //add dummy pointer
            m_children.insert(0,0);
            return true;
        }
        else {
            return false;
        }
    }
    else {
        return add(mc, c, 0, mc.mk_star()); 
    }
}

bool def::has_generalization(mc_context & mc, cond * c) {
    bool has_gen = !m_cgt.add(mc, c);
    /*
    // the unoptimized version:
    for (int i=(m_conds.size()-1); i>=0; i--) {
        if (mc.is_generalization(m_conds[i],c)) {
            SASSERT(has_gen);
            return true;
        }
    }
    SASSERT(!has_gen);
    return false;
    */
    return has_gen;
}

bool def::append_entry(mc_context & mc, cond * c, value_tuple * v) {
    if (!has_generalization(mc, c)) {
        m_conds.push_back(c);
        m_values.push_back(v);
        return true;
    }
    else {
        return false;
    }
}

void def::prepend_entry(cond * c, value_tuple * val) {
    //TODO: improve this
    ptr_vector<cond> conds;
    ptr_vector<value_tuple> values;
    conds.push_back(c);
    values.push_back(val);
    conds.append(m_conds.size(), m_conds.c_ptr());
    values.append(m_values.size(), m_values.c_ptr());
    m_conds.reset();
    m_values.reset();
    m_conds.append(conds.size(),conds.c_ptr());
    m_values.append(values.size(),values.c_ptr());
}

value_tuple * def::evaluate(mc_context & mc, cond * c) {
    for( unsigned i=0; i<m_conds.size(); i++ ){
        if (mc.is_compatible(m_conds[i], c)) {
            return m_values[i];
        }
    }
    return 0;
}

value_tuple * def::evaluate(mc_context & mc, ptr_buffer<val> & vals) {
    for( unsigned i=0; i<m_conds.size(); i++ ){
        if (mc.is_generalization(m_conds[i], vals)) {
            return m_values[i];
        }
    }
    return 0;
}

void def::simplify(mc_context & mc) {
    if (has_simplified) {
        TRACE("def_simplify",  tout << "Already simplified ? " << this << " ";
                                mc.display(tout,this);
                                tout << std::endl;);
    }
    else {
        TRACE("def_simplify", tout << "Simplify " << this << "\n";);
    }
    SASSERT(!has_simplified);
    has_simplified = true;
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
    m_partial_evaluation = false;
    m_model_repairing = true;
}

void mc_context::reset_round() {

    //clear the caches
    m_expr_to_val.reset();
    m_val_to_abs_val.reset();
    m_quant_to_cond_star.reset();
    m_expr_produced.reset();

}

//push user context
void mc_context::push() {
    
}

//pop user context
void mc_context::pop() {
    m_inst_trie.reset();
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
        m_expr_to_val.insert(e,v);
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
    value_tuple * vt = value_tuple::mk(*this, 1);
    vt->m_vec[0] = v;
    return vt;
}

value_tuple * mc_context::mk_value_tuple(ptr_buffer<val> & vals) {
    value_tuple * vt = value_tuple::mk(*this, vals.size());
    for (unsigned i=0; i<vt->get_size(); i++) {
        vt->m_vec[i] = vals[i];
    }
    return vt;
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
        return to_expr(v1)->m_value==to_expr(v2)->m_value;
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
        for( unsigned j=0; j<d2->get_num_entries(); j++ ){
            if (is_compatible(d1->get_condition(i), d2->get_condition(j))) {
                cond * c = mk_meet(d1->get_condition(i), d2->get_condition(j));
                value_tuple * v = value_tuple::mk(*this, d1->get_value(i)->get_size() + d2->get_value(j)->get_size());
                unsigned index = 0;
                for( unsigned k=0; k<d1->get_value(i)->get_size(); k++ ){
                    v->m_vec[index] = d1->get_value(i)->m_vec[k];
                    index++;
                }
                for( unsigned k=0; k<d2->get_value(j)->get_size(); k++ ){
                    v->m_vec[index] = d2->get_value(j)->m_vec[k];
                    index++;
                }
                d->append_entry(*this, c, v);
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

void mc_context::do_compose(func_decl * f, def * d) {
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
        SASSERT(ve);
        computed_vals.push_back(mk_value_tuple(ve));
    }
    d->m_values.reset();
    d->m_values.append(computed_vals.size(), computed_vals.c_ptr());
    d->has_simplified = false;
}

av_star * mc_context::mk_star() {
    return &m_star;
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

cond * mc_context::mk_star(unsigned size) {
    cond * cstar = cond::mk(*this, size);
    for (unsigned i=0; i<size; i++) {
        cstar->m_vec[i] = mk_star();
    }
    return cstar;
}

cond * mc_context::mk_star(model_constructor * mct, quantifier * q) {
    if (!m_quant_to_cond_star.contains(q)) {
        cond * cstar = cond::mk(*this, q->get_num_decls());
        for (unsigned i=0; i<cstar->get_size(); i++) {
            cstar->m_vec[i] = mct->get_projection(*this, q, i)->get_projected_default(*this);
        }
        m_quant_to_cond_star.insert(q, cstar);
        return cstar;
    }
    return m_quant_to_cond_star.find(q);
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

cond * mc_context::copy(cond * c) {
    cond * cc = cond::mk(*this, c->get_size());
    for (unsigned i=0; i<c->get_size(); i++) {
        cc->m_vec[i] = c->m_vec[i];
    }
    return cc;
}

def * mc_context::new_def() {
    void * mem = allocate(sizeof(def));
    return new (mem) def;
}


val * mc_context::mk_canon(val * v) {
    expr_ref e(m_m);
    get_expr_from_val(v, e);
    //expressions use perfect caching, values are mapped to expr, so this is canonical
    return mk_val(e);
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
    if (v->is_expr()) {
        e = to_expr(v)->get_value();
    }
    else if (v->is_int()) {
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

//display the definition
void mc_context::display(std::ostream & out, def * d) {
    for( unsigned i=0; i<d->get_num_entries(); i++ ){
        display(out, d->get_condition(i), d->get_value(i));
        out << "\n";
    }
}

lbool mc_context::check(model_constructor * mct, quantifier * q, expr_ref_buffer & instantiations, expr_ref_buffer & instantiations_star, bool mk_inst_star) {
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
        //std::cout << "Compute definition...\n";
        ptr_vector<def> empty_subst;
        d = do_check(mct, q, e, empty_subst);
        TRACE("mc_operation", tout << "Done.\n";);
       // std::cout << "Done.\n";
        TRACE("model_check",tout << "Interpretation of " << mk_pp(e,m_m) << " is : " << "\n";
                            display(tout, d);
                            tout << "\n";);
    }

    bool full_model_check = false;
    if (full_model_check && !ci.is_model_checkable()) {
        expr_ref eb(m_m);
        ci.get_non_model_checkable(eb);
        TRACE("mc_operation", tout << "Compute definition for bad...\n";);
        ptr_vector<def> approx;
        for (unsigned i=0; i<q->get_num_decls(); i++) {
            def * dx = new_def();
            projection * p = mct->get_projection(*this, q, i);
            value_tuple * def_vt;
            for (unsigned j=0; j<p->get_num_relevant_domain(); j++) {
                val * rv = p->get_relevant_domain_val(j);
                ptr_buffer<abs_val> avals;
                for (unsigned k=0; k<q->get_num_decls(); k++) {
                    avals.push_back(k==i ? mk_value(rv) : p->get_projected_default(*this));
                }
                cond * c = mk_cond(avals);
                value_tuple * rvt = mk_value_tuple(rv);
                dx->append_entry(*this, c, rvt);
                if (j==0) {
                    def_vt = rvt;
                }
            }
            //if (p->get_num_relevant_domain()==0) {
            //    def_vt = mk_value_tuple(mk_val(get_some_value(q->get_decl_sort((q->get_num_decls()-1)-i))));
            //}
            //dx->append_entry(*this, mk_star(mct, q), def_vt);
            TRACE("model_check_bad_debug",tout << "Projection for variable #" << i << " : \n";
                                            display(tout, dx);
                                            tout << "\n";);
            approx.push_back(dx);
        }

        db = do_check(mct, q, eb, approx);
        TRACE("mc_operation", tout << "Done.\n";);
        TRACE("model_check_bad",tout << "Interpretation of (bad part) " << mk_pp(eb,m_m) << " is : " << "\n";
                                display(tout, db);
                                tout << "\n";);
        if (d) {
            def * dc = mk_product(d,db);
            ptr_vector<value_tuple> valts;
            value_tuple * vttrue = mk_value_tuple(mk_val(m_true));
            value_tuple * vtfalse = mk_value_tuple(mk_val(m_false));
            TRACE("model_check_bad",tout << "Combination is : " << "\n";
                                    display(tout, dc);
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

    if (d) {
        TRACE("mc_operation", tout << "Get the instantiations...\n";);
        //std::cout << "Get instantiations...\n";
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
                    if (r==0) {
                        add_instantiation(mct, q, d->get_condition(i), instantiations, !full_model_check);
                    }
                    else {
                        add_instantiation(mct, q, d->get_condition(i), instantiations_star, !full_model_check);
                    }
                }
            }
            if (!instantiations.empty() || !mk_inst_star) {
                break;
            }
        }
        TRACE("mc_operation", tout << "Done.\n";);
        //std::cout << "Done.\n";
    }

    if (instantiations.empty() && instantiations_star.empty()) {
        return ci.is_model_checkable() ? l_true : l_undef;
    }
    else {
        return l_false;
    }
}

def * mc_context::do_check(model_constructor * mct, quantifier * q, expr * e, ptr_vector<def> & subst) {
    TRACE("model_check_debug",tout << "Model check " << mk_pp(e, m_m) << "...\n";);
    def * d = 0;
    if (is_var(e) || is_atomic_value(e)) {
        if (is_var(e)) {
            //consult an alternate definition, if provided
            unsigned vid = to_var(e)->get_idx();
            if (vid<subst.size()) {
                return subst[vid];
            }
        }
        //trivial case
        d = new_def();
        cond * star = mk_star(mct, q);
        val * v = mk_val(e);
        value_tuple * vt = mk_value_tuple(v);
        d->append_entry(*this, star, vt);
    }
    else if (is_app(e)) {
        //if it is interpreted, we may need to construct definition in a special way
        if (!is_uninterp(e)) {
            var * v;
            expr_ref t(m_m);
            bool is_flipped;
            //first check if it is an relation with a variable
            if ((mct->m_monotonic_projections || m_m.is_eq(e)) && m_cutil.is_var_relation(e, v, t, is_flipped)) {
                unsigned vid = v->get_idx();
                if (v->get_idx()>=subst.size()) {
                    TRACE("model_check_debug", tout << "Evaluate as variable relation " << mk_pp(v, m_m) << " ~ " << mk_pp(t, m_m ) << "\n";);
                    //first, model check the term
                    d = do_check(mct, q, t, subst);
                    //then, apply the variable relation on d
                    d = mk_var_relation(d, to_app(e)->get_decl(), v, is_flipped);
                }
            }
            else if (m_cutil.is_var_offset(e, v, t, is_flipped, classify_util::REQ_NON_VARIABLE)) {
                if (v->get_idx()>=subst.size()) {
                    TRACE("model_check_debug", tout << "Evaluate as variable offset " << mk_pp(v, m_m) << " + " << mk_pp(t, m_m ) << "\n";);
                    if (t) {
                        //first model check the offset if it exists
                        d = do_check(mct, q, t, subst);
                        //then, apply the variable offset on d
                        d = mk_var_offset(d, v, is_flipped);
                    }
                    else { //make it directly
                        //it should be negated (since e is not the variable itself)
                        SASSERT(is_flipped);
                        d = new_def();
                        cond * cstar = mk_star(mct, q);
                        val * vl = mk_val(v, 0, is_flipped);
                        d->append_entry(*this, cstar, mk_value_tuple(vl));
                    }
                }
            }
        }
        if (!d) {
            //otherwise, will compute product of arguments
            for (unsigned i=0; i<to_app(e)->get_num_args(); i++) {
                expr * ec = to_app(e)->get_arg(i);
                SASSERT(is_uninterp(e) || !is_var(ec) || to_var(ec)->get_idx()<subst.size());
                def * dc = do_check(mct, q, ec, subst);
                if (m_simplification) {
                    dc->simplify(*this);
                }
                d = d ? mk_product(d,dc) : dc;
            }
            TRACE("model_check_debug",if (d) {
                                        tout << "Arguments of " << mk_pp(e,m_m) << " are : " << "\n";
                                        display(tout,d);
                                        tout << "\n";
                                        });
            func_decl * f = to_app(e)->get_decl();
            if (is_uninterp(e)) {
                //uninterpreted case
                def * df;
                if (m_partial_evaluation) {
                    df = mct->get_ground_def(*this, f);
                }
                else {
                    df = mct->get_def(*this, f);
                }
                if (f->get_arity()==0) {
                    //if constant, look up the definition
                    d = new_def();
                    cond * star = mk_star(mct, q);
                    value_tuple * vt = df->get_value(0);
                    d->append_entry(*this, star, vt);
                } else {
                    //interpretation is the composition of f with arguments
                    def * d1 = mk_compose( df,d);
                    //def * d2 = mk_compose( mct->get_ground_def(*this, f),d);
                    /*
                    TRACE("test_ge",
                        tout << "Function : \n";
                        display(tout, mct->get_def(*this, f));
                        tout << "\n";
                        tout << "Ground function : \n";
                        display(tout, mct->get_ground_def(*this, f));
                        tout << "\n";
                        tout << "Arguments : \n";
                        display(tout, d);
                        tout << "\n";
                        tout << "Compare definintions: \n";
                        display(tout, d1);
                        tout << "\n";
                        tout << "Against ground: \n";
                        display(tout, d2);
                        tout << "\n";);
                    */
                    d = d1;
                }
            }
            else {
                TRACE("evaluate_debug", tout << "evaluate for " << mk_pp(e,m_m) << "\n";);
                do_compose(f, d);
            }
        }
    }
    else {
        SASSERT(false);
    }
    TRACE("model_check_debug",tout << "Interpretation of " << mk_pp(e,m_m) << " is : " << "\n";
                                display(tout, d);
                                tout << "\n";);
    SASSERT(d->get_num_entries()>0);
    return d;
}

lbool mc_context::exhaustive_instantiate(model_constructor * mct, quantifier * q, bool use_rel_domain, expr_ref_buffer & instantiations) {
    ptr_vector<expr> inst;
    return do_exhaustive_instantiate(mct, q, inst, use_rel_domain, instantiations) ? l_true : l_undef;
}

bool mc_context::do_exhaustive_instantiate(model_constructor * mct, quantifier * q, ptr_vector<expr> & inst, bool use_rel_domain, expr_ref_buffer & instantiations) {
    int index = inst.size();
    if (index==q->get_num_decls()) {
        TRACE("inst", tout << "Exhaustive instantiate " << mk_pp(q,m_m) << " with \n";
                      for (unsigned j=0; j<inst.size(); j++) {
                         tout << "   " << mk_pp(inst[j],m_m) << "\n";
                      }
                      tout << "\n";);
        expr_ref instance(m_m);
        instantiate(m_m, q, inst.c_ptr(), instance);
        instantiations.push_back(instance);
        return true;
    }
    else {
        if (use_rel_domain) {
            projection * p = mct->get_projection(*this, q, index);
            if (p->get_num_relevant_domain()==0) {
                return false;
            }
            else {
                for (unsigned i=0; i<p->get_num_relevant_domain(); i++) {
                    inst.push_back(p->get_relevant_domain(i));
                    bool ret = do_exhaustive_instantiate(mct, q, inst, use_rel_domain, instantiations);
                    inst.pop_back();
                    if (!ret) {
                        return false;
                    }
                }
                return true;
            }
        }
        else {
            //get the sort
            sort * s = q->get_decl_sort((q->get_num_decls()-1)-index);
            if (m_au.is_int(s)) {
                //TODO: use bound info?

                return false;
            }
            else if (m_bvu.is_bv_sort(s)) {
                unsigned sz = m_bvu.get_bv_size(s);
                unsigned bound = 1;
                for (unsigned i=0; i<sz; i++) { bound = bound*2; }
                for (unsigned i=0; i<bound; i++) {
                    expr_ref bvn(m_m);
                    bvn = m_bvu.mk_numeral(rational(i), sz);
                    inst.push_back(bvn);
                    do_exhaustive_instantiate(mct, q, inst, use_rel_domain, instantiations);
                    inst.pop_back();
                }
                return false;
            }
            else if (m_m.is_uninterp(s)){
                for (unsigned i=0; i<mct->get_num_universe(s); i++) {
                    inst.push_back(mct->get_universe(*this, s, i));
                    do_exhaustive_instantiate(mct, q, inst, use_rel_domain, instantiations);
                    inst.pop_back();
                }
                return false;
            }
            else {
                //TODO?
                SASSERT(false);
                return false;
            }
        }
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
                mpz ret;
                m_zm.rem(to_int(vals[0])->get_value(), to_int(vals[1])->get_value(), ret);
                return mk_val(ret);
            }
            break;
        case OP_DIV:
            {
                mpz ret;
                m_zm.div(to_int(vals[0])->get_value(), to_int(vals[1])->get_value(), ret);
                return mk_val(ret);
            }
            break;
        case OP_MOD:
            {
                mpz ret;
                m_zm.mod(to_int(vals[0])->get_value(), to_int(vals[1])->get_value(), ret);
                return mk_val(ret);
            }
            break;
        }
        //default case, use rewriter
        ptr_vector<expr> evals;
        for (unsigned i=0; i<vals.size(); i++) {
            rational ri(to_int(vals[i])->get_value());
            evals.push_back(m_au.mk_numeral(ri, true));
        }
        expr_ref nr(m_m);
        m_ar.mk_app(f, evals.size(), evals.c_ptr(), nr);
        m_expr_produced.push_back(nr);
        return mk_val(nr);
    }
    else if (f->get_family_id()==m_bvu.get_family_id()) {
        //default case, use rewriter
        ptr_vector<expr> evals;
        for (unsigned i=0; i<vals.size(); i++) {
            SASSERT(vals[i]->is_bv());
            rational ri(to_bv(vals[i])->get_value());
            evals.push_back(m_bvu.mk_numeral(ri, to_bv(vals[i])->get_size()));
        }
        expr_ref nr(m_m);
        m_bvr.mk_app(f, evals.size(), evals.c_ptr(), nr);
        m_expr_produced.push_back(nr);
        return mk_val(nr);
    }
    else if (m_m.is_eq(f)) {
        return mk_val(is_eq(vals[0], vals[1]) ? m_true : m_false);
    }
    else if (f->get_family_id()==m_m.get_basic_family_id()) {
        //boolean children should be expressions
        for (unsigned i=0; i<vals.size(); i++) {
            if (f->get_decl_kind()!=OP_ITE || i==0) {
                SASSERT(vals[i]->is_expr());
            }
        }
        switch (f->get_decl_kind()) {
        case OP_AND:
            for (unsigned i=0; i<vals.size(); i++) {
                if (m_m.is_false(to_expr(vals[i])->get_value())) {
                    return mk_val(m_false);
                }
            }
            return mk_val(m_true);
            break;
        case OP_OR:
            for (unsigned i=0; i<vals.size(); i++) {
                if (m_m.is_true(to_expr(vals[i])->get_value())) {
                    return mk_val(m_true);
                }
            }
            return mk_val(m_false);
            break;
        case OP_IFF:
            return mk_val(is_eq(vals[0], vals[1]) ? m_true : m_false);
            break;
        case OP_NOT:
             return mk_val(m_m.is_true(to_expr(vals[0])->get_value()) ? m_false : m_true);
            break;
        case OP_ITE:
            return m_m.is_true(to_expr(vals[0])->get_value()) ? vals[1] : vals[2];
            break;
        }
    }
    TRACE("evaluate_warn", tout << "Don't know how to evaluate " << mk_pp(f,m_m) << "\n";);
    SASSERT(false);
    return 0;
}


//evaluate ground term 
val * mc_context::evaluate(model_constructor * mct, expr * e, ptr_buffer<val> & vsub, bool add_entries_ensuring_non_star) {
    if (is_atomic_value(e)) {
        return mk_val(e);
    }
    else if (is_app(e)) {
        ptr_buffer<val> children;
        for (unsigned i=0; i<to_app(e)->get_num_args(); i++) {
            children.push_back(evaluate(mct, to_app(e)->get_arg(i), vsub));
        }
        func_decl * f = to_app(e)->get_decl();
        if (is_uninterp(e)) {
            def * dg = mct->get_ground_def(*this, f);
            value_tuple * vt = dg->evaluate(*this, children);
            if (!vt) {
                def * df  = mct->get_def(*this, f);
                vt = df->evaluate(*this, children);
                if (add_entries_ensuring_non_star) {
                    cond * c = mk_cond(children);
                    dg->prepend_entry(c,vt);
                    df->prepend_entry(c,vt);
                    TRACE("repair_model_debug", tout << "Prepend entry to ensure non-star evaluation : "; display(tout, c, vt); tout << " of " << mk_pp(e,m_m) << "\n";);
                }
            }
            SASSERT(vt->get_size()==1);
            TRACE("eval_term_debug", tout << "Evaluated " << mk_pp(e,m_m) << " to "; display(tout, vt->get_value(0)); tout << "\n";);
            return vt->get_value(0);
        }
        else {
                TRACE("eval_term_debug", tout << "Evaluate interpreted " << mk_pp(e,m_m) << "\n";);
            return evaluate_interp(f, children);
        }
    }
    else if (is_var(e)) {
        return vsub[to_var(e)->get_idx()];
    }
    else {
        SASSERT(false);
        return 0;
    }
}

val * mc_context::evaluate(model_constructor * mct, expr * e, bool add_entries_ensuring_non_star) {
    ptr_buffer<val> vsub;
    return evaluate(mct, e, vsub, add_entries_ensuring_non_star);
}

//repair model
bool mc_context::repair_formula(model_constructor * mct, quantifier * q, expr * e, ptr_buffer<val> & vsub, expr_ref_buffer & tsub, bool polarity) {
    TRACE("repair_model_debug", tout << "Try fixing " << mk_pp(e,m_m) << ", polarity = " << polarity << "\n";);
    if (is_app(e)) {
        //try to make the formula with var_subst equal to polarity
        if ((m_m.is_or(e) && polarity) || (m_m.is_and(e) && !polarity)) {
            for (unsigned i=0; i<to_app(e)->get_num_args(); i++) {
                if (repair_formula(mct, q, to_app(e)->get_arg(i), vsub, tsub, polarity)) {
                    return true;
                }
            }
            return false;
        }
        else if (m_m.is_not(e)) {
            return repair_formula(mct, q, to_app(e)->get_arg(0), vsub, tsub, !polarity);
        }
        else if (m_m.is_eq(e)) {
            for (unsigned i=0; i<2; i++) {
                expr * ec = to_app(e)->get_arg(i);
                if (is_app(ec) && is_uninterp(to_app(ec)->get_decl())) {
                    //evaluate the other side
                    expr * eco = to_app(e)->get_arg(i==0 ? 1 : 0);
                    val * ecov = evaluate(mct, eco, vsub);
                    if (repair_term(mct, q, ec, vsub, tsub, ecov)) {
                        return true;
                    }
                }
            }
        }
        else if (is_uninterp(to_app(e)->get_decl())) {
            //predicate case
            return repair_term(mct, q, e, vsub, tsub, mk_val(polarity ? m_true : m_false));
        }
    }
    return false;
}

bool mc_context::repair_term(model_constructor * mct, quantifier * q, expr * t, ptr_buffer<val> & vsub, expr_ref_buffer & tsub, val * v) {
    //try to make the term with var_subst equal to v
    SASSERT(is_uninterp(t));
    //evaluate the arguments
    ptr_buffer<val> args;
    for (unsigned i=0; i<to_app(t)->get_num_args(); i++) {
        args.push_back(evaluate(mct, to_app(t)->get_arg(i), vsub));
    }
    func_decl * f = to_app(t)->get_decl();
    def * dg = mct->get_ground_def(*this, f);
    if (!dg->evaluate(*this, args)) {
        TRACE("repair_model", tout << "Can be fixed by adding (";
                              for (unsigned i=0; i<args.size(); i++) {
                                  if (i>0) tout << ", ";
                                  display(tout, args[i]);
                              }
                              tout << ") -> ";
                              display(tout,v);
                              tout << " to " << mk_pp(f,m_m) << "\n";);
        // do the repair
        def * df = mct->get_def(*this, f);
        //make the condition from the values
        ptr_buffer<abs_val> avals;
        for (unsigned i=0; i<args.size(); i++) {
            val * vi = mk_canon(args[i]);
            avals.push_back(mk_value(vi));

            //make sure value is in the relevant domain
            projection * p = mct->get_projection(*this,f,i);
            if (!p->has_relevant_domain_val(vi)) {
                //do this by substituting for current expression
                expr_ref tis(m_m);
                if (is_var(to_app(t)->get_arg(i))) {
                    tis = tsub[to_var(to_app(t)->get_arg(i))->get_idx()];
                    SASSERT(is_eq(vsub[to_var(to_app(t)->get_arg(i))->get_idx()],vi));
                }
                else {
                    var_subst vs(m_m);
                    vs(to_app(t)->get_arg(i),tsub.size(),tsub.c_ptr(), tis);
                    if (!m_expr_produced.contains(tis)) {
                        m_expr_produced.push_back(tis);
                    }
                    TRACE("repair_model_debug", tout << "Must evaluate " << mk_pp(tis,m_m) << " to ensure ground definition is set...\n";);
                    val * ve = evaluate(mct, tis, vsub, true);
                    if (!is_eq(ve,vi)) {
                        TRACE("repair_model_warn", tout << mk_pp(tis,m_m) << " evaluated is not equal to the expectation.\n";
                                                    display(tout,ve);
                                                    tout << " != ";
                                                    display(tout,vi);
                                                    tout << std::endl;);
                        SASSERT(false);
                    }
                }
                
                TRACE("repair_model_debug", tout << "Need to add to relevant domain " << mk_pp(tis,m_m) << " -> ";
                                            display(tout, vi); tout << "\n";);
                p->add_relevant_domain(tis, vi);
            }

        }
        cond * c = mk_cond(avals);
        value_tuple * vt = mk_value_tuple(v);
        dg->prepend_entry(c, vt);
        df->prepend_entry(c, vt);
        return true;
    }
    else {
        return false;
    }
}

void mc_context::add_instantiation(model_constructor * mct, quantifier * q, cond * c, expr_ref_buffer & instantiations, bool & repaired,
                                  bool filterEval, bool filterRepair, bool filterCache) {
    //since condition may contain values made from direct evaluation, we must canonize the condition before consulting externally
    cond * cic = mk_canon(c);
    //get the corresponding instantiation from the model construction object
    expr_ref_buffer inst(m_m);
    bool inst_found_expr;
    mct->get_inst(*this, q, cic, inst, inst_found_expr);
    for (unsigned j=0; j<inst.size(); j++) {
        if (!m_expr_produced_global.contains(inst[j])) {
            m_expr_produced_global.push_back(inst[j]);
        }
    }
    TRACE("inst",tout << "Instantiate " << mk_pp(q,m_m) << " with \n";
                    for (unsigned j=0; j<inst.size(); j++) {
                            tout << "   " << mk_pp(inst[j],m_m) << "\n";
                    }
                    tout << "\n";
                    //tout << "Filters : " << filterEval << " " << filterRepair << " " << filterCache << "\n";
                    if (!inst_found_expr) tout << "    *** did not find expressions in relevant domain.\n";);
    //if (!inst_found_expr) std::cout << "    *** did not find expressions in relevant domain.\n";
    bool addInstantiation = true;
    //evaluate again with values of instantiation
    /*  1st unoptimized:
    //should be guarenteed to falsify at least the good part
    def * di = do_check(mct, q, inst_body, empty_subst, false);
    TRACE("mc_inst_debug", tout << "Redoing check, definition is : \n";
                        display(tout, di);
                        tout << "\n";);
    SASSERT(di->get_num_entries()==1);
    //SASSERT(m_m.is_false(to_expr(di->get_value(0)->get_value(0))->get_value()));
    */
    /* 2nd unoptimized:
    //use a variable substitution (assumes that q does not have nested quantifiers)
    var_subst vs(m_m);
    expr_ref inst_body(m_m);
    vs(q->get_expr(),inst.size(),inst.c_ptr(), inst_body);
    TRACE("mc_inst_debug", tout << "Redo check on " << mk_pp(inst_body,m_m) << "\n";);
    val * v = evaluate(mct, inst_body, val_subs);
    */
    //evaluate arguments, evaluate body directly
    if (filterEval || filterRepair) {
        if (addInstantiation) {
            ptr_buffer<val> val_subs;
            for (unsigned j=0; j<inst.size(); j++) {
                if (cic->get_value(j)->is_value()) {
                    val_subs.push_back(to_value(cic->get_value(j))->get_value());
                }
                else {
                    //evaluate to get value of term
                    val * ve = evaluate(mct, inst[(inst.size()-1)-j]);
                    val_subs.push_back(ve);
                }
            }
            if (filterEval) {
                val * v = evaluate(mct, q->get_expr(), val_subs);
                SASSERT(v->is_expr());
                if (!m_m.is_false(to_expr(v)->get_value())) {
                    TRACE("inst",tout << "...instantiation evaluated to true in model.\n";);
                    addInstantiation = false;
                }
            }
            if (addInstantiation && filterRepair && m_model_repairing) {
                if (repair_formula(mct, q, q->get_expr(), val_subs, inst, true)) {
                    //TODO: set instantiation false
                    repaired = true;
                    addInstantiation = false;
                    TRACE("inst",tout << "...instantiation was repaired.\n";);
                }
                else {
                    TRACE("repair_model", tout << "Could not repair!\n";);
                }
            }
        }
    }
    if (addInstantiation) {
        if (filterCache) {
            inst_trie * it;
            if (!m_inst_trie.find(q, it)) {
                void * mem = allocate(sizeof(inst_trie));
                it = new (mem) inst_trie;
                m_inst_trie.insert(q,it);
            }
            if (!it->add(*this, inst)) {
                addInstantiation = false;
                TRACE("inst",tout << "...instantiation was already added to cache.\n";);
            }
        }
        if (addInstantiation) {
            expr_ref instance(m_m);
            instantiate(m_m, q, inst.c_ptr(), instance);
            instantiations.push_back(instance);
        }
    }
}


eval_node * mc_context::mk_eval_node( expr * e, ptr_vector<eval_node> & active, ptr_buffer<eval_node> & vars, 
                                      obj_map< expr, eval_node *> & evals, expr * parent) {
    eval_node * ene;
    if (evals.find(e, ene)) {
        return ene;
    }
    else {
        void * mem = allocate(sizeof(eval_node));
        ene = new (mem) eval_node(e);
        if (!is_ground(e) && is_app(e)) {
            for (unsigned i=0; i<to_app(e)->get_num_args(); i++) {
                expr * ec = to_app(e)->get_arg(i);
                if (is_atomic_value(ec)) {
                    ene->m_children_eval_count++;
                    ene->m_children.push_back(0);
                }
                else if (is_uninterp(e) && m_cutil.is_var_offset(ec, classify_util::REQ_GROUND)) {
                    ene->m_children_eval_count++;
                    ene->m_vars_to_bind++;
                    ene->m_children.push_back(0);
                }
                else {
                    eval_node * enec = mk_eval_node(ec, active, vars, evals, e);
                    enec->add_parent(ene);
                }
            }
        }
        if (is_ground(e) || ene->can_evaluate()) {
            active.push_back(ene);
        }
        if (is_var(e)) {
            unsigned vid = to_var(e)->get_idx();
            vars[vid] = ene;
        }
        evals.insert(e, ene);
        return ene;
    }
}

lbool mc_context::eval_check(model_constructor * mct, quantifier * q, expr_ref_buffer & instantiations, bool & repaired) {
    ptr_vector<eval_node> active;
    ptr_buffer<eval_node> vars;
    vars.resize(q->get_num_decls(),0);
    obj_map< expr, eval_node *> evals;
    mk_eval_node(q->get_expr(), active, vars, evals);

    //std::random_shuffle(active.begin(), active.end());

    TRACE("eval_check", tout << "Run eval check on " << mk_pp(q,m_m) << "\n";
                        tout << "------------------\n";
                        tout << "Evaluation terms are summarized : \n";
                        for (obj_map< expr, eval_node *>::iterator it = evals.begin(); it != evals.end(); ++it) {
                            expr * e = it->m_key;
                            eval_node * en = it->m_value;
                            tout << "   " << mk_pp(e,m_m) << " ";
                            if (active.contains(en)) {
                                tout << "*active*";
                            }
                            tout << "\n";
                        }
                        );
    //std::cout << "Eval check " << mk_pp(q,m_m) << "..." << std::endl;
    cond * curr_cond = mk_star(mct,q);
    repaired = false;
    if (!do_eval_check(mct, q, active, vars, curr_cond, instantiations, 0, repaired)) {
        TRACE("eval_check", tout << "Eval check failed on quantifier " << mk_pp(q,m_m) << "\n";);
    }
    //std::cout << "Done." << std::endl;

    if (instantiations.empty()) {
        return l_undef;
    }
    else {
        return l_false;
    }
}

bool mc_context::do_eval_check(model_constructor * mct, quantifier * q, ptr_vector<eval_node> & active, ptr_buffer<eval_node> & vars, 
                               cond * curr_cond, expr_ref_buffer & instantiations, unsigned var_bind_count, bool & repaired) {
    unsigned prev_size = active.size();
    if (!active.empty()) {
        unsigned best_index = active.size()-1;
        unsigned max_score = 0;
        for (unsigned i=0; i<active.size(); i++) {
            unsigned ii = (active.size()-1)-i;
            if (active[ii]->can_evaluate()) {
                unsigned score = 1 + active[ii]->m_vars_to_bind; //TODO?
                //get score
                if (score>max_score) {
                    best_index = ii;
                }
            }
        }
        eval_node * en = active[best_index];
        active.erase(active.begin()+best_index);
        expr * e = en->get_expr();
        TRACE("eval_check_debug", tout << "Process " << mk_pp(e,m_m) << "\n";
                                  tout << "Current condition : ";
                                  display(tout,curr_cond);
                                  tout << "\n";);
        val * result = 0;
        if (is_ground(e)) {
            //just use the evaluator
            result = evaluate(mct, e);
        }
        else {
            //evaluate the expression
            ptr_buffer<val> children;
            sbuffer<unsigned> var_to_bind;
            for (unsigned i=0; i<to_app(e)->get_num_args(); i++) {
                if (en->get_child(i)) {
                    children.push_back(en->get_child(i)->get_evaluation());
                }
                else {
                    expr * ec = to_app(e)->get_arg(i);
                    if (is_atomic_value(ec)) {
                        children.push_back(mk_val(ec));
                    }
                    else {
                        var * v;
                        expr_ref t(m_m);
                        bool is_flipped;
                        if (is_uninterp(e) && m_cutil.is_var_offset(ec, v, t, is_flipped, classify_util::REQ_GROUND)) {
                            //check if v is already bound
                            unsigned vid = v->get_idx();
                            val * val_made = 0;
                            if (curr_cond->get_value(vid)->is_value()) {
                                val_made = to_value(curr_cond->get_value(vid))->get_value();
                            }
                            else {
                                if (!var_to_bind.contains(vid)) {
                                    var_to_bind.push_back(vid);
                                }
                            }
                            //check if there is an offset
                            if (t) {
                                SASSERT(is_ground(t));
                                //make the val for t
                                val * vt = evaluate(mct, t);
                                if (val_made) {
                                    val_made = mk_add(vt, is_flipped ? mk_negate(val_made) : val_made);
                                }
                                else {
                                    val_made = mk_val(v, vt, is_flipped);
                                }
                            }
                            else if (!val_made) {    //otherwise, and if not already bound
                                val_made = is_flipped ? mk_val(v, 0, is_flipped) : mk_val(v);
                            }
                            children.push_back(val_made);
                        }
                        else {
                            //don't know how to evaluate (start trying relevant domain?)
                            SASSERT(false);
                        }
                    }
                }
            }
            func_decl * f = to_app(e)->get_decl();
            //compute the definition
            if (is_uninterp(f)) {
                def * df = mct->get_def(*this,f);
                if (!var_to_bind.empty()) {
                    var_bind_count += var_to_bind.size();
                    //need to compute a compose
                    def * da = new_def();
                    da->append_entry(*this, curr_cond, mk_value_tuple(children));
                    //now, do compose
                    def * dc = mk_compose(df,da);
                    TRACE("eval_check_debug", tout << "Evaled, Made definition : \n";
                                              display(tout,dc);
                                              tout << "\n";);
                    ptr_vector<eval_node> new_active;
                    if (var_bind_count<q->get_num_decls()) {
                        //have each newly bound variable notify that they evaluate
                        for (unsigned j=0; j<var_to_bind.size(); j++) {
                            if (vars[var_to_bind[j]]) {
                                vars[var_to_bind[j]]->notify_evaluation(new_active);
                            }
                        }
                        //as well as this
                        en->notify_evaluation(new_active);
                        if (!new_active.empty()) {
                            TRACE("eval_check_debug", 
                                for (unsigned i=0; i<new_active.size(); i++) {
                                    tout << "Now active : " << mk_pp(new_active[i]->get_expr(),m_m) << "\n";
                                }
                                );
                            new_active.append(active.size(), active.c_ptr());
                        }
                    }
                    //process each entry in the compose
                    for (unsigned i=0; i<dc->get_num_entries(); i++) {
                        cond * cc = dc->get_condition(i);
                        //try each entry
                        bool binds_all_vars = true;
                        for (unsigned j=0; j<var_to_bind.size(); j++) {
                            if (!cc->get_value(var_to_bind[j])->is_value()) {
                                binds_all_vars = false;
                                break;
                            }
                            else if (vars[var_to_bind[j]]) {
                                vars[var_to_bind[j]]->m_value = to_value(cc->get_value(var_to_bind[j]))->get_value();
                            }
                        }
                        if (binds_all_vars) {
                            if (var_bind_count<q->get_num_decls()) {
                                en->m_value = dc->get_value(i)->get_value(0);
                                if (new_active.empty()) {
                                    if (en->get_expr()!=q->get_expr() || m_m.is_false(to_expr(en->m_value)->get_value())) {
                                        SASSERT(!active.empty() || en->get_expr()==q->get_expr());
                                        if (!do_eval_check(mct, q, active, vars, cc, instantiations, var_bind_count, repaired)) {
                                            return false;
                                        }
                                    }
                                }
                                else {
                                    if (!do_eval_check(mct, q, new_active, vars, cc, instantiations, var_bind_count, repaired)) {
                                        return false;
                                    }
                                }
                            }
                            else {
                                //just do the evaluation now
                                TRACE("eval_check_debug", tout << "Add instantiation "; display(tout, curr_cond); tout << "\n";);
                                //we have an instantiation
                                //add_instantiation(mct, q, cc, instantiations, true);
                                add_instantiation(mct, q, cc, instantiations, repaired, true, true, true);
                            }
                        }
                    }
                    if (var_bind_count<q->get_num_decls()) {
                        en->unnotify_evaluation();
                        for (unsigned j=0; j<var_to_bind.size(); j++) {
                            if (vars[var_to_bind[j]]) {
                                vars[var_to_bind[j]]->unnotify_evaluation();
                            }
                        }
                    }
                }
                else {
                    //just evaluate
                    //TRACE("eval_check_debug", tout << "Definition is "; display(tout,df); tout << "\n";);
                    result = df->evaluate(*this, children)->get_value(0);

                    //--------------------test
                    /*
                    ptr_buffer<val> vsub;
                    for (unsigned i=0; i<curr_cond->get_size(); i++) {
                        if (curr_cond->get_value(i)->is_value()) {
                            vsub.push_back(to_value(curr_cond->get_value(i))->get_value());
                        }
                        else {
                            vsub.push_back(0);
                        }
                    }
                    result = evaluate(mct, e, vsub, true);
                    */
                    //---------------------end test
                }
            }
            else {
                TRACE("eval_term_debug", tout << "evaluate for " << mk_pp(e, m_m) << "\n";);
                //just evaluate
                result = evaluate_interp(f, children);
            }
        }
        // if processing a simple result, just recurse
        if (result) {
            TRACE("eval_check_debug", tout << "Evaled, lookup got "; display(tout, result); tout << "\n";);
            ptr_vector<eval_node> new_active;
            en->notify_evaluation(new_active);
            en->m_value = result;
            if (new_active.empty()) {
                if (en->get_expr()!=q->get_expr() || m_m.is_false(to_expr(en->m_value)->get_value())) {
                    if (active.empty() && en->get_expr()!=q->get_expr()) {
                        SASSERT(var_bind_count<q->get_num_decls());
                        return false;
                    }
                    else {
                        if (!do_eval_check(mct, q, active, vars, curr_cond, instantiations, var_bind_count, repaired)) {
                            return false;
                        }
                    }
                }
            }
            else {
                TRACE("eval_check_debug", 
                    for (unsigned i=0; i<new_active.size(); i++) {
                        tout << "Now active : " << mk_pp(new_active[i]->get_expr(),m_m) << "\n";
                    }
                    );
                new_active.append(active.size(), active.c_ptr());
                if (!do_eval_check(mct, q, new_active, vars, curr_cond, instantiations, var_bind_count, repaired)) {
                    return false;
                }
            }
            en->m_value = 0;
            en->unnotify_evaluation();
        }
        //put it back into active
        active.push_back(en);
    }
    else {
        SASSERT(false);
        //TRACE("eval_check_debug", tout << "Add instantiation "; display(tout, curr_cond); tout << "\n";);
        //we have an instantiation (curr_cond)
        //add_instantiation(mct, q, curr_cond, instantiations);
        //add_instantiation(mct, q, curr_cond, instantiations, repaired, false, true);
    }
    SASSERT(active.size()==prev_size);
    return true;
}



void eval_node::notify_evaluation(ptr_vector<eval_node> & active) {
    for (unsigned i=0; i<m_parents.size(); i++) {
        m_parents[i]->m_children_eval_count++;
        TRACE("eval_node", tout << "parent inc " << m_parents[i]->m_children_eval_count << " / " << to_app(m_parents[i]->get_expr())->get_num_args() << "\n";);
        if (m_parents[i]->can_evaluate()) {
            SASSERT(!active.contains(m_parents[i]));
            active.push_back(m_parents[i]);
        }
    }
}
void eval_node::unnotify_evaluation() {
    for (unsigned i=0; i<m_parents.size(); i++) {
        m_parents[i]->m_children_eval_count--;
    }
}
