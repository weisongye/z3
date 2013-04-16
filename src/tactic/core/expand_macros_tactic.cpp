/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    expand_macros_tactic.cpp

Abstract:
    
    Expand simple macros in a goal or assertion stack
    
Author:

    Leonardo de Moura (leonardo) 2013-02-11

Revision History:

--*/
#include"tactical.h"
#include"assertion_stream.h"
#include"th_rewriter.h"
#include"macro_substitution.h"
#include"extension_model_converter.h"
#include"for_each_expr.h"

class expand_macros_tactic : public tactic {
    th_rewriter *            m_rw;

    struct set_rw {
        expand_macros_tactic & m;
        set_rw(expand_macros_tactic & _m, th_rewriter & r):m(_m) {
            #pragma omp critical (tactic_cancel)
            {
                m.m_rw  = &r;
            }
        }
        ~set_rw() {
            #pragma omp critical (tactic_cancel)
            {
                m.m_rw  = 0;
            }
        }
    };

    struct collect_decl_params_proc {
        obj_hashtable<func_decl> & m_decl_params;
        collect_decl_params_proc(obj_hashtable<func_decl> & decl_params):m_decl_params(decl_params) {}
        void operator()(var const * n) { }
        void operator()(app const * n) { 
            func_decl_info * info = n->get_decl()->get_info(); 
            if (info) {
                unsigned num = info->get_num_parameters();
                for (unsigned i = 0; i < num; i++) {
                    parameter const & p = info->get_parameter(i);
                    if (p.is_ast() && is_func_decl(p.get_ast())) {
                        m_decl_params.insert(to_func_decl(p.get_ast()));
                    }
                }
            }
        }
        void operator()(quantifier const * n) {}
    };

    static void collect_decl_params(assertion_stream & g, obj_hashtable<func_decl> & decl_params) {
        expr_fast_mark1 visited;
        collect_decl_params_proc proc(decl_params);
        unsigned size = g.size(); 
        for (unsigned i = g.qhead(); i < size; i++) {
            expr * f = g.form(i);
            quick_for_each_expr(proc, visited, f);
        }
    }

    struct found {}; 
    struct decl_proc {
        obj_hashtable<func_decl> const & m_decls;

        decl_proc(obj_hashtable<func_decl> const & ds):m_decls(ds) {}
        void operator()(var const * n) { }
        void operator()(app const * n) { 
            if (n->get_num_args() > 0 && 
                n->get_family_id() == null_family_id && 
                m_decls.contains(n->get_decl())) 
                throw found(); 
        }
        void operator()(quantifier const * n) {}
    };
    
    // Return true if n contains one of the declarations in decls
    static bool contains(expr * n, obj_hashtable<func_decl> const & decls) {
        decl_proc p(decls);
        try {
            quick_for_each_expr(p, n);
        }
        catch (found) {
            return true;
        }
        return false;
    }

    static bool is_macro_head(assertion_stream & g, expr * h, unsigned num_decls) {
        if (is_app(h) && 
            to_app(h)->get_family_id() == null_family_id && 
            to_app(h)->get_num_args() == num_decls &&
            !g.is_frozen(to_app(h)->get_decl())) {
            sbuffer<bool> found;
            found.resize(num_decls, false);
            for (unsigned i = 0; i < to_app(h)->get_num_args(); i++) {
                expr * c = to_app(h)->get_arg(i);
                if (!is_var(c))
                    return false;
                unsigned vidx = to_var(c)->get_idx(); 
                if (vidx >= num_decls || found[vidx])
                    return false; // variable out of range or variable already found.
                found[vidx] = true;
            }
            DEBUG_CODE({
                    for (unsigned i = 0; i < found.size(); i++) {
                        SASSERT(found[i]);
                    }
                });
            return true;
        }
        else {
            return false;
        }
    }

    static func_decl * is_macro(assertion_stream & g, expr * head, expr * def, unsigned num_decls, obj_hashtable<func_decl> & found_macros, obj_hashtable<func_decl> const & forbidden) {
        if (is_macro_head(g, head, num_decls)) {
            func_decl * f = to_app(head)->get_decl();
            if (found_macros.contains(f) || forbidden.contains(f))
                return 0; // f is already selected as a macro
            found_macros.insert(f);
            if (def && contains(def, found_macros)) {
                found_macros.erase(f);
                return 0; // cycle detected
            }
            // keep f in the list of macros
            return f;
        }
        else {
            return 0;
        }
    }

    static func_decl * is_macro(assertion_stream & g, quantifier * q, obj_hashtable<func_decl> & found_macros, obj_hashtable<func_decl> const & forbidden) {
        ast_manager & m = g.m();
        unsigned num_decls = q->get_num_decls();
        expr * b = q->get_expr();
        expr * lhs, * rhs;
        if (m.is_eq(b, lhs, rhs) || m.is_iff(b, lhs, rhs)) {
            func_decl * f = is_macro(g, lhs, rhs, num_decls, found_macros, forbidden);
            if (f) return f;
            return is_macro(g, rhs, lhs, num_decls, found_macros, forbidden);
        }
        else
            return 0;       
    }

    static func_decl * is_bool_macro(assertion_stream & g, quantifier * q, obj_hashtable<func_decl> & found_macros, quantifier_ref & qprime, obj_hashtable<func_decl> const & forbidden) {
        ast_manager & m = g.m();
        unsigned num_decls = q->get_num_decls();
        expr * b = q->get_expr();
        func_decl * f = is_macro(g, b, 0, num_decls, found_macros, forbidden);
        if (f) {
            qprime = m.update_quantifier(q, m.mk_iff(b, m.mk_true()));
            return f;
        }
        else if (m.is_not(b, b)) {
            f = is_macro(g, b, 0, num_decls, found_macros, forbidden);
            if (f) {
                qprime = m.update_quantifier(q, m.mk_iff(b, m.mk_false()));
                return f;
            }
        }
        return 0;
    }

    static void find_macros(assertion_stream & g, macro_substitution & ms, obj_hashtable<func_decl> const & forbidden) {
        ast_manager & m = g.m();
        obj_hashtable<func_decl> found_macros;
        bool proofs_enabled = g.proofs_enabled();
        unsigned size = g.size(); 
        quantifier_ref qprime(m);
        proof_ref pr(m);
        for (unsigned i = g.qhead(); i < size; i++) {
            expr * a = g.form(i);
            if (is_quantifier(a)) {
                quantifier * q = to_quantifier(a);
                func_decl * f = is_macro(g, q, found_macros, forbidden);
                if (f != 0) {
                    ms.insert(f, q, g.pr(i), g.dep(i));
                    g.add_definition(f, q, g.pr(i), g.dep(i));
                    // remove quantifier
                    g.update(i, m.mk_true(), 0, 0);
                }
                else {
                    func_decl * f = is_bool_macro(g, q, found_macros, qprime, forbidden);
                    if (f != 0) {
                        if (proofs_enabled) {
                            pr = m.mk_modus_ponens(g.pr(i), m.mk_rewrite(q, qprime));
                        }
                        else {
                            pr = 0;
                        }
                        ms.insert(f, qprime, pr, g.dep(i));
                        g.add_definition(f, qprime, pr, g.dep(i));
                        // remove quantifier
                        g.update(i, m.mk_true(), 0, 0);
                    }
                }
            }
        }
    }

    bool apply_core(assertion_stream & g, obj_hashtable<func_decl> const & forbidden) {
        SASSERT(g.is_well_sorted());
        ast_manager & m = g.m();
        stream_report report("expand_macros", g);
        macro_substitution ms(m, g.unsat_core_enabled(), g.proofs_enabled());
        find_macros(g, ms, forbidden);
        if (!ms.empty()) {
            TRACE("expand_macros_detail", tout << "MACROS:\n"; ms.display(tout); tout << "===============\n"; g.display(tout););
            th_rewriter rw(m);
            rw.set_macro_substitution(&ms);
            set_rw s(*this, rw);
            
            expr_ref   new_curr(m);
            proof_ref  new_pr(m);
            unsigned size = g.size();
            for (unsigned idx = g.qhead(); idx < size; idx++) {
                if (g.inconsistent())
                    break;
                expr * curr = g.form(idx);
                rw(curr, new_curr, new_pr);
                if (g.proofs_enabled()) {
                    proof * pr = g.pr(idx);
                    new_pr    = m.mk_modus_ponens(pr, new_pr);
                }
                g.update(idx, new_curr, new_pr, g.dep(idx));
            }
            TRACE("expand_macros", g.display(tout););
            return true;
        }
        SASSERT(g.is_well_sorted());
        return false;
    }

    void apply(assertion_stream & g) {
        obj_hashtable<func_decl> forbidden;
        collect_decl_params(g, forbidden);
        while (!g.inconsistent() && apply_core(g, forbidden)) {
            // keep removing macros...
            g.elim_redundancies();
        }
    }
    
public:    
    expand_macros_tactic():m_rw(0) {}

    virtual tactic * translate(ast_manager & m) {
        return alloc(expand_macros_tactic);
    }

    virtual void updt_params(params_ref const & p) {}
    virtual void collect_param_descrs(param_descrs & r) {}
    
    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        TRACE("expand_macros_detail", g->display(tout););
        mc = 0; pc = 0; core = 0; result.reset();
        goal_and_emc2stream s(*(g.get()));
        apply(s);
        if (g->models_enabled())
            mc = s.mc();
        g->inc_depth();
        result.push_back(g.get());
    }

    virtual void operator()(assertion_stack & s) {
        assertion_stack2stream strm(s);
        apply(strm);
    }
                            
    virtual void set_cancel(bool f) {
        if (m_rw) {
            m_rw->set_cancel(f);
        }
    }

    virtual void cleanup() {}
};

tactic * mk_expand_macros_tactic(ast_manager & m, params_ref const & p) {
    return alloc(expand_macros_tactic);
}
