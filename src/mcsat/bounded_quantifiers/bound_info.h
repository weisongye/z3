/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    bound_info.h

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-01-17.

--*/
#ifndef _BOUND_INFO_H_
#define _BOUND_INFO_H_

#include"ast.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"th_rewriter.h"

// m_l and m_u are signed bounds (also includes Int)
// m_ul and m_uu and unsigned bounds
// m_bd is the new body of the quantifier
// m_var_order specify the order of variable bounds
//   variable v_0 has fixed (ground) bounds
//   variable v_i has fixed bounds if all variables v_j for j<i have fixed bounds
class bound_info
{
private:
    ast_manager & m_m;
    arith_util & m_au;
    bv_util & m_bvu;
    bool collect_literals(expr * e, expr_ref_buffer & lits );
    bool get_var_monomial(expr * e, expr_ref & var, expr_ref & coeff);
    bool is_ground_bnd_vars(expr * e);
    void get_bv_auto_bound(bool isLower, bool isSigned, sort * s, expr_ref & result);
    void is_bounded_quantifier_iter(expr_ref_buffer & lits, expr_ref_buffer& bnds, 
                                    sbuffer<int>& new_bnd_vars, expr_ref_buffer & new_bnds, 
                                    sbuffer<int>& new_bnds_from_vars, sbuffer<bool> & new_bnds_signs,
                                    expr_ref_buffer & new_ovf);
public:
    bound_info( ast_manager & m, arith_util & au, bv_util & bvu, quantifier* q ) : m_m(m), m_au(au), m_bvu(bvu), m_q(q), m_l(m), m_u(m), m_sl(m), m_su(m), m_body(m){
        for (unsigned i = 0; i < q->get_num_decls(); i++) {
            m_l.push_back(m.mk_false());
            m_u.push_back(m.mk_false());
            m_sl.push_back(m.mk_false());
            m_su.push_back(m.mk_false());
        }
        m_is_valid = false;
        m_is_trivial_sat = false;
    }
    bool m_is_valid;
    bool m_is_trivial_sat;
    quantifier * m_q;
    expr_ref_buffer m_l;
    expr_ref_buffer m_u;
    expr_ref_buffer m_sl;
    expr_ref_buffer m_su;
    expr_ref_buffer m_body;
    sbuffer<int> m_var_order;

    bool compute();

    bool is_valid() { return m_is_valid; }
    bool is_trivial_sat() { return m_is_trivial_sat; }
    bool is_bound( unsigned idx );
    bool is_int_bound( unsigned idx ) { return !m_m.is_false(m_l[idx]) && !m_m.is_false(m_u[idx]); }
    bool is_bv_unsigned_bound( unsigned idx ) { return is_int_bound(idx); }
    bool is_bv_signed_bound( unsigned idx ) { return !m_m.is_false(m_sl[idx]) && !m_m.is_false(m_su[idx]); }
    expr* get_lower_bound( unsigned idx ) { return is_bv_signed_bound(idx) ? m_sl[idx] : m_l[idx]; }
    expr* get_upper_bound( unsigned idx ) { return is_bv_signed_bound(idx) ? m_su[idx] : m_u[idx]; }
    void print( const char * tc );
    //return true if all lower bounds are zero
    bool is_normalized();
    //get body
    //  this is the original body without literals that were used for bounds,
    //  and possibly additional literals in the case of bit vectors
    void get_body( expr_ref& body, bool inc_bounds = true );
    // get quantifier 
    quantifier* get_quantifier();
    // get variable order index for idx
    int get_var_order_index( unsigned idx );
    // apply rewriter to bounds
    void apply_rewrite(th_rewriter& as);
};


#endif
