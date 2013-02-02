/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    expr_bound_propagator.cpp

Abstract:

    Wrapper for bound_propagator class.
    It allows us to process bounds of Z3 expression objects.

Author:

    Leonardo de Moura (leonardo) 2013-02-01.

Revision History:

--*/
#include"expr_bound_propagator.h"
#include"bound_propagator.h"
#include"ast_pp.h"

struct expr_bound_propagator::imp {
    ast_manager &          m;
    params_ref             m_params;
    unsynch_mpq_manager    nm;
    small_object_allocator m_allocator;
    bound_propagator       bp;
    arith_util             m_util;
    typedef bound_propagator::var a_var;
    obj_map<expr, a_var>   m_expr2var;
    expr_ref_vector        m_exprs;
    ptr_vector<expr>       m_var2expr;

    typedef numeral_buffer<mpq, unsynch_mpq_manager> scoped_mpq_buffer;
    typedef svector<a_var> var_buffer;                          
    
    scoped_mpq_buffer      m_num_buffer;
    var_buffer             m_var_buffer;

    struct scope {
        unsigned m_exprs_trail;
        unsigned m_var2expr_trail;
    };

    svector<scope>         m_scopes;

    // parameters
    bool                   m_arith_lhs; // only consider equalities and disequalities in arith-lhs form          
    
    imp(ast_manager & _m, params_ref const & p):
        m(_m),
        m_allocator("expr-bound-propagator"),
        bp(nm, m_allocator, p),
        m_util(m),
        m_exprs(m),
        m_num_buffer(nm) {
        updt_params_core(p);
    }

    void updt_params_core(params_ref const & p) {
        m_arith_lhs = p.get_bool("arith_lhs", false);
    }

    void updt_params(params_ref const & p) {
        m_params = p;
        updt_params_core(p);
        bp.updt_params(p);
    }

    void display_bounds(std::ostream & out) {
        unsigned sz = m_var2expr.size();
        mpq  k;
        bool strict;
        unsigned ts;
        for (unsigned x = 0; x < sz; x++) {
            if (bp.lower(x, k, strict, ts)) 
                out << nm.to_string(k) << " " << (strict ? "<" : "<=");
            else
                out << "-oo <";
            expr * v = m_var2expr.get(x);
            if (v)
                out << " " << mk_pp(v, m) << " ";
            else
                out << " x!" << x << " ";
            if (bp.upper(x, k, strict, ts)) 
                out << (strict ? "<" : "<=") << " " << nm.to_string(k);
            else
                out << "< oo";
            out << "\n";
        }
    }

    a_var mk_var(expr * t) {
        if (m_util.is_to_real(t))
            t = to_app(t)->get_arg(0);
        a_var x;
        if (m_expr2var.find(t, x))
            return x;
        x = m_var2expr.size();
        bp.mk_var(x, m_util.is_int(t));
        m_var2expr.push_back(t);
        m_exprs.push_back(t);
        m_expr2var.insert(t, x);
        return x;
    }

    a_var mk_fresh_var(bool is_int) {
        a_var x;
        x = m_var2expr.size();
        bp.mk_var(x, is_int);
        m_var2expr.push_back(0);
        return x;
    }

    // Auxiliary function for expr2linear_pol
    void process_monomial(expr * mon, scoped_mpq_buffer & as, var_buffer & xs, scoped_mpq & b, bool neg) {
        rational c_val;
        expr * c, * x;
        if (m_util.is_mul(mon, c, x) && m_util.is_numeral(c, c_val)) {
            as.push_back(c_val.to_mpq());
            if (neg)
                nm.neg(as.back());
            xs.push_back(mk_var(x));
        }
        else if (m_util.is_numeral(mon, c_val)) {
            if (neg)
                nm.sub(b, c_val.to_mpq(), b);
            else
                nm.add(b, c_val.to_mpq(), b);
        }
        else {
            if (neg) 
                as.push_back(mpq(-1));
            else
                as.push_back(mpq(1));
            xs.push_back(mk_var(mon));
        }
    }

    void expr2linear_pol(expr * t, scoped_mpq_buffer & as, var_buffer & xs, scoped_mpq & b, bool neg) {
        if (m_util.is_add(t)) {
            unsigned num = to_app(t)->get_num_args();
            for (unsigned i = 0; i < num; i++) {
                process_monomial(to_app(t)->get_arg(i), as, xs, b, neg);
            }
        }
        else {
            process_monomial(t, as, xs, b, neg);
        }
    }

    bool all_int(var_buffer const & xs) const {
        for (unsigned i = 0; i < xs.size(); i++) {
            if (!bp.is_int(xs[i]))
                return false;
        }
        return true;
    }

    enum kind { EQ, LE, GE };
    
    kind neg(kind k) {
        if (k == LE)
            return GE;
        else if (k == GE)
            return LE;
        else
            return EQ;
    }

    bool assert_expr(expr * t) {
        bool sign = false;
        while (m.is_not(t, t))
            sign = !sign;
        bool strict = false;
        kind k;
        if (m.is_eq(t)) {
            if (sign)
                return false;
            k = EQ;
        } 
        else if (m_util.is_le(t)) {
            if (sign) {
                k = GE;
                strict = true;
            }
            else {
                k = LE;
            }
        }
        else if (m_util.is_ge(t)) {
            if (sign) {
                k = LE;
                strict = true;
            }
            else {
                k = GE;
            }
        }
        else {
            return false;
        }
        expr * lhs = to_app(t)->get_arg(0);
        expr * rhs = to_app(t)->get_arg(1);
        if (m_util.is_numeral(lhs)) {
            std::swap(lhs, rhs); 
            if (k == LE)
                k = GE;
            else if (k == GE)
                k = LE;
        }
        rational c;
        a_var x = UINT_MAX;
        scoped_mpq c_q(nm);
        if (!m_util.is_numeral(rhs, c)) {
            if (m_arith_lhs)
                return false;
            // formula is not in arith lhs form
            m_num_buffer.reset();
            m_var_buffer.reset();
            expr2linear_pol(lhs, m_num_buffer, m_var_buffer, c_q, false);
            expr2linear_pol(rhs, m_num_buffer, m_var_buffer, c_q, true);
            nm.neg(c_q);
            x = mk_fresh_var(all_int(m_var_buffer));
            m_num_buffer.push_back(mpq(-1));
            m_var_buffer.push_back(x);
            bp.mk_eq(m_num_buffer.size(), m_num_buffer.c_ptr(), m_var_buffer.c_ptr());
        }
        else {
            if (!m_expr2var.find(lhs, x)) {
                if (m_util.is_add(lhs) || m_util.is_mul(lhs)) {
                    m_num_buffer.reset();
                    m_var_buffer.reset();
                    expr2linear_pol(lhs, m_num_buffer, m_var_buffer, c_q, false);
                    if (nm.is_zero(c_q)) {
                        x = mk_var(lhs);
                    }
                    else { 
                        if (m_arith_lhs) 
                            return false;
                        // formula is not in lhs form
                        x = mk_fresh_var(all_int(m_var_buffer));
                        nm.neg(c_q);
                    }
                    nm.add(c_q, c.to_mpq(), c_q);
                    m_num_buffer.push_back(mpq(-1));
                    m_var_buffer.push_back(x);
                    bp.mk_eq(m_num_buffer.size(), m_num_buffer.c_ptr(), m_var_buffer.c_ptr());
                }
                else {
                    x = mk_var(lhs);
                    nm.set(c_q, c.to_mpq());
                }
            }
            else {
                SASSERT(x != UINT_MAX);
                nm.set(c_q, c.to_mpq());
            }
        }
        SASSERT(x != UINT_MAX);
        if (k == EQ) {
            SASSERT(!strict);
            bp.assert_lower(x, c_q, false);
            bp.assert_upper(x, c_q, false);
        }
        else if (k == LE) {
            bp.assert_upper(x, c_q, strict);
        }
        else {
            SASSERT(k == GE);
            bp.assert_lower(x, c_q, strict);
        }
        return true;
    }

    void push() {
        bp.push();
        m_scopes.push_back(scope());
        scope & s = m_scopes.back();
        s.m_exprs_trail    = m_exprs.size();
        s.m_var2expr_trail = m_var2expr.size();
    }

    void pop(unsigned num_scopes) {
        bp.pop(num_scopes);
        unsigned new_lvl    = m_scopes.size() - num_scopes;
        scope & s           = m_scopes[new_lvl];
        for (unsigned i = s.m_var2expr_trail; i < m_var2expr.size(); i++) {
            expr * t = m_var2expr[i];
            if (t)
                m_expr2var.erase(t);
        }
        m_var2expr.shrink(s.m_var2expr_trail);
        m_exprs.shrink(s.m_exprs_trail);
        m_scopes.shrink(new_lvl);
    }
    
    bool has_lower(expr * t) const {
        a_var x;
        return m_expr2var.find(t, x) && bp.has_lower(x);
    }
    
    bool has_upper(expr * t) const {
        a_var x;
        return m_expr2var.find(t, x) && bp.has_upper(x);
    }
    
    bool lower(expr * t, mpq & k, bool & strict) {
        unsigned ts;
        a_var x;
        if (m_expr2var.find(t, x))
            return bp.lower(x, k, strict, ts);
        return false;
    }

    bool upper(expr * t, mpq & k, bool & strict) {
        unsigned ts;
        a_var x;
        if (m_expr2var.find(t, x))
            return bp.upper(x, k, strict, ts);
        return false;
    }

    bool poly_lower(expr * p, mpq & k, bool & strict) {
        if (!m_util.is_add(p))
            return false;
        m_num_buffer.reset();
        m_var_buffer.reset();
        scoped_mpq b(nm);
        expr2linear_pol(p, m_num_buffer, m_var_buffer, b, false);
        if (!nm.is_zero(b))
            return false;
        return bp.lower(m_var_buffer.size(), m_num_buffer.c_ptr(), m_var_buffer.c_ptr(), k, strict);
    }

    bool poly_upper(expr * p, mpq & k, bool strict) {
        if (!m_util.is_add(p))
            return false;
        m_num_buffer.reset();
        m_var_buffer.reset();
        scoped_mpq b(nm);
        expr2linear_pol(p, m_num_buffer, m_var_buffer, b, false);
        if (!nm.is_zero(b))
            return false;
        return bp.upper(m_var_buffer.size(), m_num_buffer.c_ptr(), m_var_buffer.c_ptr(), k, strict);
    }
};

expr_bound_propagator::expr_bound_propagator(ast_manager & m, params_ref const & p) {
    m_imp = alloc(imp, m, p);
}

expr_bound_propagator::~expr_bound_propagator() {
    dealloc(m_imp);
}

expr_bound_propagator::numeral_manager & expr_bound_propagator::nm() const {
    return m_imp->nm;
}

void expr_bound_propagator::updt_params(params_ref const & p) {
    m_imp->updt_params(p);
}

void expr_bound_propagator::get_param_descrs(param_descrs & r) {
    bound_propagator::get_param_descrs(r);
    r.insert("arith_lhs", CPK_BOOL, "only consider atoms in arith-lhs normal form (default: false)");
}

void expr_bound_propagator::collect_statistics(statistics & st) const {
    m_imp->bp.collect_statistics(st);
}

void expr_bound_propagator::reset_statistics() {
    m_imp->bp.reset_statistics();
}

bool expr_bound_propagator::assert_expr(expr * t) {
    return m_imp->assert_expr(t);
}
    
bool expr_bound_propagator::has_lower(expr * t) const {
    return m_imp->has_lower(t);
}
 
bool expr_bound_propagator::has_upper(expr * t) const {
    return m_imp->has_upper(t);
}

bool expr_bound_propagator::lower(expr * x, mpq & k, bool & strict) const {
    return m_imp->lower(x, k, strict);
}

bool expr_bound_propagator::upper(expr * x, mpq & k, bool & strict) const {
    return m_imp->upper(x, k, strict);
}

bool expr_bound_propagator::poly_lower(expr * p, mpq & k, bool & strict) {
    return m_imp->poly_lower(p, k, strict);
}

bool expr_bound_propagator::poly_upper(expr * p, mpq & k, bool & strict) {
    return m_imp->poly_upper(p, k, strict);
}

void expr_bound_propagator::propagate() {
    return m_imp->bp.propagate();
}

bool expr_bound_propagator::inconsistent() const {
    return m_imp->bp.inconsistent();
}

void expr_bound_propagator::reset() {
    ast_manager & m = m_imp->m;
    params_ref p    = m_imp->m_params;
    #pragma omp critical (expr_bound_propagator) 
    {
        dealloc(m_imp);
        m_imp = alloc(imp, m, p);
    }
}

void expr_bound_propagator::push() {
    m_imp->push();
}

void expr_bound_propagator::pop(unsigned num_scopes) {
    m_imp->pop(num_scopes);
}

unsigned expr_bound_propagator::num_exprs() const {
    return m_imp->m_exprs.size();
}

expr * expr_bound_propagator::get_expr(unsigned i) const {
    return m_imp->m_exprs.get(i);
}

void expr_bound_propagator::set_cancel(bool f) {
    #pragma omp critical (expr_bound_propagator) 
    {
        m_imp->bp.set_cancel(f);
    }
}

void expr_bound_propagator::display(std::ostream & out) const {
    m_imp->display_bounds(out);
}
