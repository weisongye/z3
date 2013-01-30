/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    bounded_quantifiers_tactic.cpp

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-01-17.

--*/
#include"tactical.h"
#include"datatypes_quantifiers_tactic.h"
#include"tactic.h"
#include"rewriter_def.h"
#include"var_subst.h"
#include"ast_pp.h"
#include"th_rewriter.h"
#include"datatype_decl_plugin.h"
#include"assertion_stream.h"

class split_datatype_quantifiers_tactic : public tactic {

    struct rw_cfg : public default_rewriter_cfg {
    private:
        bool process(quantifier* q, int index, var_subst & vs, var_shifter & vsh, 
                     ptr_buffer<sort> & sorts, sbuffer< symbol > & symbols, expr_ref_buffer & subs, expr_ref_buffer & conj) {
            if (index < 0) {
                TRACE("split_datatype_quantifiers-debug", tout << "Quantifier : " << mk_pp( q, m_m ) << "\n";);
                //add to conjunction
                expr_ref q_c(m_m);
                //make the substituted body
                q_c = q->get_expr();
                TRACE("split_datatype_quantifiers-debug", tout << "Body : " << mk_pp( q_c, m_m ) << "\n";);
                int var_change = sorts.size() - q->get_num_decls();
                if (var_change > 0) {
                    vsh(q_c, q->get_num_decls(), var_change, 0, q_c);
                    TRACE("split_datatype_quantifiers-debug", tout << "Shifted Body : " << mk_pp( q_c, m_m ) << "\n";);
                }
                // [Leo]: The for-loop should be inside the TRACE
                for (unsigned i = 0; i < subs.size(); i++) {
                    TRACE("split_datatype_quantifiers-debug", tout << "subsitutions : " << i << " -> " << mk_pp( subs[i], m_m ) << "\n";);
                }
                vs(q_c, subs.size(), subs.c_ptr(), q_c);
                if (var_change < 0) {
                    vsh(q_c, q->get_num_decls(), var_change, 0, q_c);
                    TRACE("split_datatype_quantifiers-debug", tout << "Shifted Body : " << mk_pp( q_c, m_m ) << "\n";);
                }
                TRACE("split_datatype_quantifiers-debug", tout << "Substituted Body : " << mk_pp(q_c, m_m ) << "\n";);
                //reverse sorts and symbols
                sbuffer< sort* > rev_sorts;
                sbuffer< symbol > rev_symbols;
                for (unsigned i = 0; i < sorts.size(); i++ ){
                    rev_sorts.push_back( sorts[ sorts.size()-i-1 ] );
                    rev_symbols.push_back( symbols[ symbols.size()-i-1 ] );
                }
                q_c = m_m.mk_quantifier(true, sorts.size(), rev_sorts.c_ptr(), rev_symbols.c_ptr(), q_c);
                TRACE("split_datatype_quantifiers-debug", tout << "New quantifier : " << mk_pp(q_c, m_m) << "\n";);
                conj.push_back( q_c );
                return true;
            }
            else {
                //process the variable
                sort * s = q->get_decl_sort(index);
                if (m_dtu.is_datatype(s)) {
                    ptr_vector<func_decl> const * cons = m_dtu.get_datatype_constructors(s);
                    for (unsigned i=0; i<m_dtu.get_datatype_num_constructors(s); i++) {
                        ptr_buffer<sort> new_sorts;
                        sbuffer<symbol> new_symbols;
                        new_sorts.append(sorts.size(), sorts.c_ptr());
                        new_symbols.append(symbols);
                        //split based on constructor
                        func_decl * f = (*cons)[i];
                        expr_ref_buffer args(m_m);
                        //introduce new quantified variables for each subfield
                        for (unsigned j = 0; j < f->get_arity(); ++j) {
                            sort * s2 = f->get_domain(j);
                            args.push_back(m_m.mk_var(new_sorts.size(), s2));
                            new_sorts.push_back(s2);
                            //new_symbols.push_back(m_m.get_fresh_symbol(q->get_decl_name(index), j));
                            new_symbols.push_back(q->get_decl_name(index)); //TODO
                        }
                        subs.push_back(m_m.mk_app(f,args.size(), args.c_ptr()));
                        bool proc = process(q, index-1, vs, vsh, new_sorts, new_symbols, subs, conj);
                        subs.pop_back();
                        if (!proc) {
                            return false;
                        }
                    }
                    return true;
                }
                else {
                    subs.push_back(m_m.mk_var(sorts.size(), s));
                    sorts.push_back(s);
                    symbols.push_back(q->get_decl_name(index));
                    bool proc = process(q, index-1, vs, vsh, sorts, symbols, subs, conj);
                    symbols.pop_back();
                    sorts.pop_back();
                    subs.pop_back();
                    return proc;
                }
            }
        }
    public:
        ast_manager & m_m;
        datatype_util m_dtu;
        rw_cfg(ast_manager & _m):m_m(_m), m_dtu(_m){}
        
        bool reduce_quantifier(quantifier * old_q, 
                               expr * new_body, 
                               expr * const * new_patterns, 
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {
            quantifier * q = m_m.update_quantifier(old_q, old_q->get_num_patterns(), new_patterns, old_q->get_num_no_patterns(), new_no_patterns, new_body);
            if (q->is_forall()) {
                TRACE("split_datatype_quantifiers",tout << "Process " << mk_pp(q,m_m) << "\n";);
                // keep track of variables
                ptr_buffer<sort> new_sorts;
                sbuffer< symbol > new_symbols;
                expr_ref_buffer subs(m_m);
                expr_ref_buffer conj(m_m);
                var_subst vs(m_m,false);
                var_shifter vsh(m_m);
                int index = q->get_num_decls() - 1;
                if (process(q, index, vs, vsh, new_sorts, new_symbols, subs, conj)) {
                    //we rewrote the quantifier into a conjunction
                    result = conj.size()>1 ? m_m.mk_and(conj.size(), conj.c_ptr()) : ( conj.size()==1 ? conj[0] : m_m.mk_false() );
                    return true;
                }
            }
            return false;
        }
    };

    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;
        rw(ast_manager & m):
            rewriter_tpl<rw_cfg>(m, false, m_cfg),
            m_cfg(m) {
        }
    };
    
    rw            m_rw;
    params_ref    m_params;
public:
    split_datatype_quantifiers_tactic(ast_manager & m, params_ref const & p):
	m_rw(m),
	m_params(p) {
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(split_datatype_quantifiers_tactic, m, m_params);
    }

    virtual ~split_datatype_quantifiers_tactic() {}

    virtual void updt_params(params_ref const & p) { m_params = p; }

    virtual void collect_param_descrs(param_descrs & r) { }

    void apply(assertion_stream & g) {
        TRACE("split_datatype_quantifiers", g.display(tout););
        fail_if_proof_generation("split_datatype_quantifiers_tactic", g.proofs_enabled());
        ast_manager & m = g.m();
        SASSERT(g.is_well_sorted());
        stream_report report("split_datatype_quantifiers", g);
        unsigned sz = g.size();
        expr_ref new_curr(m);
        for (unsigned i = g.qhead(); i < sz; i++) {
            expr * curr = g.form(i);
            m_rw(curr, new_curr);
            g.update(i, new_curr, 0, g.dep(i));
        }
        TRACE("split_datatype_quantifiers", g.display(tout););
        SASSERT(g.is_well_sorted());
    }

    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        mc = 0; pc = 0; core = 0;
        goal2stream s(*(g.get()));
        apply(s);
        g->inc_depth();
        result.push_back(g.get());
    }

    virtual void operator()(assertion_stack & s) {
        assertion_stack2stream strm(s);
        apply(strm);
    }
    
    virtual void cleanup() {
        m_rw.cleanup();
    }
    
    virtual void set_cancel(bool f) {
        m_rw.set_cancel(f);
    }
};

tactic * mk_split_datatype_quantifiers_tactic(ast_manager & m, params_ref const & p) {
    return alloc(split_datatype_quantifiers_tactic, m, p);
}
