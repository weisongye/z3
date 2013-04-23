/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    model_check.cpp

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-04-22.

--*/

#include"exhaustive_check.h"
#include"model_construct.h"
#include"ast_pp.h"
#include"var_subst.h"

using namespace qsolver;

exhaustive_check::exhaustive_check(ast_manager & _m) : 
    m_m(_m), m_au(_m), m_bvu(_m) {

}

lbool exhaustive_check::run(mc_context & mc, model_constructor * mct, quantifier * q, bool use_rel_domain, expr_ref_buffer & instantiations) {
    ptr_vector<expr> inst;
    return do_exhaustive_instantiate(mc, mct, q, inst, use_rel_domain, instantiations) ? l_true : l_undef;
}

bool exhaustive_check::do_exhaustive_instantiate(mc_context & mc, model_constructor * mct, quantifier * q, ptr_vector<expr> & inst, bool use_rel_domain, expr_ref_buffer & instantiations) {
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
            projection * p = mct->get_projection(mc, q, index);
            if (p->get_num_relevant_domain()==0) {
                return false;
            }
            else {
                for (unsigned i=0; i<p->get_num_relevant_domain(); i++) {
                    inst.push_back(p->get_relevant_domain(i));
                    bool ret = do_exhaustive_instantiate(mc, mct, q, inst, use_rel_domain, instantiations);
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
                    do_exhaustive_instantiate(mc, mct, q, inst, use_rel_domain, instantiations);
                    inst.pop_back();
                }
                return false;
            }
            else if (m_m.is_uninterp(s)){
                for (unsigned i=0; i<mct->get_num_universe(s); i++) {
                    inst.push_back(mct->get_universe(mc, s, i));
                    do_exhaustive_instantiate(mc, mct, q, inst, use_rel_domain, instantiations);
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
