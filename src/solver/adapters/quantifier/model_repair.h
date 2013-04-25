/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    model_repair.h

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-04-25.

--*/
#ifndef _MODEL_REPAIR_H_
#define _MODEL_REPAIR_H_

#include"ast.h"
#include"lbool.h"
#include"model_check.h"

namespace qsolver
{

class mc_context;
class model_constructor;

class model_repair
{
    friend class model_constructor;
protected:
    // options
    bool m_active;
    bool m_tracking;
    bool m_tracking_rec_repair;
protected:
    bool do_repair_formula(mc_context & mc, model_constructor * mct, quantifier * q, expr * e, expr_ref_buffer & vsub, expr_ref_buffer & tsub, bool polarity, 
                           ptr_buffer<annot_entry> & fail_entry, ptr_buffer<expr> & fail_value, ptr_buffer<func_decl> & fail_func, annot_entry * & inst_reason);
    bool do_repair_term(mc_context & mc, model_constructor * mct, quantifier * q, expr * t, expr_ref_buffer & vsub, expr_ref_buffer & tsub, expr * v, 
                         ptr_buffer<annot_entry> & fail_entry, ptr_buffer<expr> & fail_value, ptr_buffer<func_decl> & fail_func, annot_entry * & inst_reason);
    expr * ensure_interpretation(mc_context & mc, model_constructor * mct, expr * t, expr_ref_buffer & vsub, expr_ref_buffer & tsub, 
                                 quantifier * q_reason = 0, annot_entry * inst_reason = 0);
    //managers for expressions
    ast_manager & m_m;
    //map from repair entries to the repair why they were added
    ptr_addr_map<annot_entry, ptr_vector<quantifier> > m_repair_quant;
    ptr_addr_map<annot_entry, ptr_vector<annot_entry> > m_repair_inst;
    ptr_vector<annot_entry> m_repairs_permanent;
    //get repair
    bool is_permanent(annot_entry * c) { return m_repairs_permanent.contains(c); }
    void push_permanent_repair(annot_entry * c) { m_repairs_permanent.push_back(c); }
    void pop_permanent_repair() { m_repairs_permanent.pop_back(); }
public:
    //stats
    bool m_was_repaired;
    unsigned m_stat_repairs;
public:
    model_repair(ast_manager & _m);
    //reset the round
    void reset_round(mc_context & mc);
    //repair model
    bool repair_formula(mc_context & mc, model_constructor * mct, quantifier * q, expr_ref_buffer & vsub, expr_ref_buffer & tsub, expr_ref_buffer & instantiations);
    //
    bool append_entry_to_simple_def(mc_context & mc, model_constructor * mct, func_decl * f, annot_entry * c, quantifier * q_repair = 0, annot_entry * inst_repair = 0);
    void append_repair(annot_entry * c, quantifier * q_repair, annot_entry * inst_repair);
};

}

#endif
