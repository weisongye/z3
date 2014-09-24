#include "check_relation.h"
#include "dl_relation_manager.h"
#include "qe_util.h"
#include "ast_util.h"
#include "smt_kernel.h"


namespace datalog {

    check_relation::check_relation(check_relation_plugin& p, relation_signature const& sig, relation_base* r):
        relation_base(p, sig),
        m(p.get_ast_manager()),
        m_relation(r),
        m_fml(m) {
        m_relation->to_formula(m_fml);
    }
    check_relation::~check_relation() {
        m_relation->deallocate();
    }
    void check_relation::check_equiv(expr* f1, expr* f2) const { 
        get_plugin().check_equiv(f1, f2); 
    }
    void check_relation::consistent_formula() {
        expr_ref fml(m);
        m_relation->to_formula(fml);
        if (m_fml != fml) {
            IF_VERBOSE(0, display(verbose_stream() << "relation does not have a consistent formula"););
        }
    }
    expr_ref check_relation::mk_eq(relation_fact const& f) const {
        relation_signature const& sig = get_signature();
        expr_ref_vector conjs(m);
        for (unsigned i = 0; i < sig.size(); ++i) {
            conjs.push_back(m.mk_eq(m.mk_var(i, sig[i]), f[i]));
        }
        return expr_ref(mk_and(m, conjs.size(), conjs.c_ptr()), m);
    }

    expr_ref check_relation::ground(expr* fml) const {
        relation_signature const& sig = get_signature();
        var_subst sub(m, false);
        expr_ref_vector vars(m);
        for (unsigned i = 0; i < sig.size(); ++i) {
            vars.push_back(m.mk_const(symbol(i), sig[i]));
        }
        expr_ref result(m);
        sub(fml, vars.size(), vars.c_ptr(), result);
        return result;
    }

    void check_relation::add_fact(const relation_fact & f) {
        expr_ref fml1(m);
        m_relation->add_fact(f);
        m_relation->to_formula(fml1);
        m_fml = m.mk_or(m_fml, mk_eq(f));        
        check_equiv(ground(m_fml), ground(fml1));
        m_fml = fml1;
    }
    void check_relation::add_new_fact(const relation_fact & f) {
        expr_ref fml1(m);
        m_relation->add_new_fact(f);
        m_relation->to_formula(fml1);
        m_fml = m.mk_or(m_fml, mk_eq(f));
        check_equiv(ground(m_fml), ground(fml1));
        m_fml = fml1;
    }
    bool check_relation::empty() const {
        bool result = m_relation->empty();
        if (result && !m.is_false(m_fml)) {
            check_equiv(m.mk_false(), ground(m_fml));
        }
        return result;
    }
    bool check_relation::fast_empty() const {
        bool result = m_relation->fast_empty();
        if (result && !m.is_false(m_fml)) {
            check_equiv(m.mk_false(), ground(m_fml));
        }
        return result;
    }
    void check_relation::reset() {
        m_relation->reset();
        m_fml = m.mk_false();
    }

    bool check_relation::contains_fact(const relation_fact & f) const {
        bool result = m_relation->contains_fact(f);
        expr_ref fml1(m), fml2(m);
        fml1 = mk_eq(f);
        fml2 = m.mk_and(m_fml, fml1);
        if (result) {
            check_equiv(ground(fml1), ground(fml2));            
        }
        else if (!m.is_false(m_fml)) {
            check_equiv(ground(fml2), m.mk_false());            
        }
        return result;
    }
    check_relation * check_relation::clone() const {
        check_relation* result = check_relation_plugin::get(get_plugin().mk_empty(get_signature()));
        result->m_relation->deallocate();
        result->m_relation = m_relation->clone();
        result->m_relation->to_formula(result->m_fml);
        if (m_fml != result->m_fml) {
            check_equiv(ground(m_fml), ground(result->m_fml));
        }
        return result;
    }
    check_relation * check_relation::complement(func_decl* f) const {
        check_relation* result = check_relation_plugin::get(get_plugin().mk_empty(get_signature()));
        result->m_relation->deallocate();
        result->m_relation = m_relation->complement(f);
        result->m_relation->to_formula(result->m_fml);
        expr_ref fml(m);
        fml = m.mk_not(m_fml);
        check_equiv(ground(fml), ground(result->m_fml));
        return result;
    }
    void check_relation::to_formula(expr_ref& fml) const {
        fml = m_fml;
    }

    check_relation_plugin& check_relation::get_plugin() const {
        return static_cast<check_relation_plugin&>(relation_base::get_plugin());
    }

    void check_relation::display(std::ostream& out) const {
        m_relation->display(out);
        out << m_fml << "\n";
    }

    // -------------

    check_relation_plugin::check_relation_plugin(relation_manager& rm):
        relation_plugin(check_relation_plugin::get_name(), rm),
        m(rm.get_context().get_manager()),
        m_base(0) {
    }
    check_relation_plugin::~check_relation_plugin() {
    }
    check_relation& check_relation_plugin::get(relation_base& r) {
        return dynamic_cast<check_relation&>(r);
    }
    check_relation* check_relation_plugin::get(relation_base* r) {
        return r?dynamic_cast<check_relation*>(r):0;
    }
    check_relation const & check_relation_plugin::get(relation_base const& r) {
        return dynamic_cast<check_relation const&>(r);        
    }

    bool check_relation_plugin::can_handle_signature(const relation_signature & sig) {
        return m_base->can_handle_signature(sig);
    }
    relation_base * check_relation_plugin::mk_empty(const relation_signature & sig) {
        relation_base* r = m_base->mk_empty(sig);
        return alloc(check_relation, *this, sig, r);
    }
    relation_base * check_relation_plugin::mk_full(func_decl* p, const relation_signature & s) {
        relation_base* r = m_base->mk_full(p, s);
        return alloc(check_relation, *this, s, r);
    }

    class check_relation_plugin::join_fn : public convenient_relation_join_fn {
        scoped_ptr<relation_join_fn> m_join;
    public:
        join_fn(relation_join_fn* j,
                 const relation_signature & o1_sig, const relation_signature & o2_sig, unsigned col_cnt,
                 const unsigned * cols1, const unsigned * cols2)
            : convenient_join_fn(o1_sig, o2_sig, col_cnt, cols1, cols2), m_join(j) 
        {}
        virtual ~join_fn() {}
        virtual relation_base * operator()(const relation_base & r1, const relation_base & r2) {
            check_relation const& t1 = get(r1);
            check_relation const& t2 = get(r2);
            check_relation_plugin& p = t1.get_plugin();
            relation_base* r = (*m_join)(t1.rb(), t2.rb());
            p.verify_join(r1, r2, *r, m_cols1.size(), m_cols1.c_ptr(), m_cols2.c_ptr());
            return alloc(check_relation, p, r->get_signature(), r);
        }
    };    

    relation_join_fn * check_relation_plugin::mk_join_fn(
        const relation_base & t1, const relation_base & t2,
        unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {        
        relation_join_fn* j = m_base->mk_join_fn(get(t1).rb(), get(t2).rb(), col_cnt, cols1, cols2);
        return j?alloc(join_fn, j, t1.get_signature(), t2.get_signature(), col_cnt, cols1, cols2):0;        
    }

    void check_relation_plugin::verify_filter_project(
        relation_base const& src, relation_base const& dst, 
        app* cond, unsigned_vector const& removed_cols) {
        expr_ref fml1(m), fml2(m);
        src.to_formula(fml1);
        dst.to_formula(fml2);
        fml1 = m.mk_and(cond, fml1);
        verify_project(src, fml1, dst, fml2, removed_cols);
    }

    void check_relation_plugin::verify_project(
        relation_base const& src, 
        relation_base const& dst, 
        unsigned_vector const& removed_cols) {
        expr_ref fml1(m), fml2(m);
        src.to_formula(fml1);
        dst.to_formula(fml2);
        verify_project(src, fml1, dst, fml2, removed_cols);
    }
    void check_relation_plugin::verify_project(
        relation_base const& src, expr* f1, 
        relation_base const& dst, expr* f2,
        unsigned_vector const& removed_cols) {
        expr_ref fml1(m);
        expr_ref fml2(m);
        expr_ref_vector vars1(m), vars2(m);
        ptr_vector<sort> bound;
        svector<symbol> names;
        relation_signature const& sig1 = src.get_signature();
        relation_signature const& sig2 = dst.get_signature();
        for (unsigned i = 0; i < sig2.size(); ++i) {
            vars2.push_back(m.mk_const(symbol(i), sig2[i]));
        }
        for (unsigned i = 0, j = 0, k = 0; i < sig1.size(); ++i) {
            if (j < removed_cols.size() && removed_cols[j] == i) {
                std::ostringstream strm;
                strm << "x" << j;
                bound.push_back(sig1[i]);                
                names.push_back(symbol(strm.str().c_str()));
                vars1.push_back(m.mk_var(j, sig1[i]));
                ++j;
            }
            else {
                vars1.push_back(vars2[k].get());
                SASSERT(m.get_sort(vars2[k].get()) == sig1[i]);
                ++k;
            }
        }
        var_subst sub(m, false);
        sub(f1, vars1.size(), vars1.c_ptr(), fml1);
        sub(f2, vars2.size(), vars2.c_ptr(), fml2);
        bound.reverse();        
        fml1 = m.mk_exists(bound.size(), bound.c_ptr(), names.c_ptr(), fml1);
        check_equiv(fml1, fml2);
    }

    void check_relation_plugin::verify_permutation(
        relation_base const& src, relation_base const& dst, 
        unsigned_vector const& cycle) {
        unsigned_vector perm;
        relation_signature const& sig1 = src.get_signature();
        relation_signature const& sig2 = dst.get_signature();
        for (unsigned i = 0; i < sig1.size(); ++i) {
            perm.push_back(i);
        }
        for (unsigned i = 0; i < cycle.size(); ++i) {
            unsigned j = (i + 1)%cycle.size();
            unsigned col1 = cycle[i];
            unsigned col2 = cycle[j];
            perm[col2] = col1;
        }
        for (unsigned i = 0; i < perm.size(); ++i) {
            SASSERT(sig2[perm[i]] == sig1[i]);
        }
        expr_ref_vector sub(m);
        for (unsigned i = 0; i < perm.size(); ++i) {
            sub.push_back(m.mk_var(perm[i], sig1[i]));
        }
        var_subst subst(m, false);
        expr_ref fml1(m), fml2(m);
        src.to_formula(fml1);
        dst.to_formula(fml2);
        subst(fml1, sub.size(), sub.c_ptr(), fml1);
        expr_ref_vector vars(m);
        for (unsigned i = 0; i < sig2.size(); ++i) {
            vars.push_back(m.mk_const(symbol(i), sig2[i]));            
        }

        subst(fml1, vars.size(), vars.c_ptr(), fml1);
        subst(fml2, vars.size(), vars.c_ptr(), fml2);
        
        check_equiv(fml1, fml2);
    }

    void check_relation_plugin::verify_join(relation_base const& t1, relation_base const& t2, relation_base const& t,
                                  unsigned sz, unsigned const* cols1, unsigned const* cols2) {
        ast_manager& m = get_ast_manager();
        expr_ref fml1(m), fml2(m), fml3(m);
        
        relation_signature const& sig1 = t1.get_signature();
        relation_signature const& sig2 = t2.get_signature();
        relation_signature const& sig  = t.get_signature();
        var_ref var1(m), var2(m);
        t1.to_formula(fml1);
        t2.to_formula(fml2);
        t.to_formula(fml3);
        var_subst sub(m, false);
        expr_ref_vector vars(m);
        for (unsigned i = 0; i < sig2.size(); ++i) {
            vars.push_back(m.mk_var(i + sig1.size(), sig2[i]));
        }
        sub(fml2, vars.size(), vars.c_ptr(), fml2);
        fml1 = m.mk_and(fml1, fml2);
        for (unsigned i = 0; i < sz; ++i) {
            unsigned v1 = cols1[i];
            unsigned v2 = cols2[i];
            var1 = m.mk_var(v1, sig1[v1]);
            var2 = m.mk_var(v2 + sig1.size(), sig2[v2]);
            fml1 = m.mk_and(m.mk_eq(var1, var2), fml1);
        }
        vars.reset();
        for (unsigned i = 0; i < sig.size(); ++i) {
            std::stringstream strm;
            strm << "x" << i;
            vars.push_back(m.mk_const(symbol(strm.str().c_str()), sig[i]));            
        }
        sub(fml1, vars.size(), vars.c_ptr(), fml1);
        sub(fml3, vars.size(), vars.c_ptr(), fml3);
        check_equiv(fml1, fml3);
    }

    void check_relation_plugin::verify_filter(expr* fml0, relation_base const& t, expr* cond) {
        expr_ref fml1(m), fml2(m);
        fml1 = m.mk_and(fml0, cond);
        t.to_formula(fml2);
        
        relation_signature const& sig = t.get_signature();
        expr_ref_vector vars(m);
        var_subst sub(m, false);
        for (unsigned i = 0; i < sig.size(); ++i) {
            std::stringstream strm;
            strm << "x" << i;
            vars.push_back(m.mk_const(symbol(strm.str().c_str()), sig[i]));            
        }
        sub(fml1, vars.size(), vars.c_ptr(), fml1);
        sub(fml2, vars.size(), vars.c_ptr(), fml2);
        check_equiv(fml1, fml2);
    }

    void check_relation_plugin::check_equiv(expr* fml1, expr* fml2) {
        TRACE("doc", tout << mk_pp(fml1, m) << "\n";
              tout << mk_pp(fml2, m) << "\n";);
        smt_params fp;
        smt::kernel solver(m, fp);
        expr_ref tmp(m);
        tmp = m.mk_not(m.mk_eq(fml1, fml2));        
        solver.assert_expr(tmp);
        lbool res = solver.check();
        if (res == l_false) {
            IF_VERBOSE(3, verbose_stream() << "verified\n";);
        }
        else {
            IF_VERBOSE(3, verbose_stream() << "NOT verified " << res << "\n";
                       verbose_stream() << mk_pp(fml1, m) << "\n";
                       verbose_stream() << mk_pp(fml2, m) << "\n";);
            throw 0;
        }
    }

    void check_relation_plugin::verify_union(expr* fml0, relation_base const& src, relation_base const& dst, relation_base const* delta) {
        expr_ref fml1(m), fml2(m), fml3(m);
        src.to_formula(fml1);
        dst.to_formula(fml2);
        fml1 = m.mk_or(fml1, fml0);
        relation_signature const& sig = dst.get_signature();
        expr_ref_vector vars(m);
        var_subst sub(m, false);
        for (unsigned i = 0; i < sig.size(); ++i) {
            std::stringstream strm;
            strm << "x" << i;
            vars.push_back(m.mk_const(symbol(strm.str().c_str()), sig[i]));            
        }
        sub(fml1, vars.size(), vars.c_ptr(), fml1);
        sub(fml2, vars.size(), vars.c_ptr(), fml2);

        check_equiv(fml1, fml2);

        if (delta) {
            delta->to_formula(fml3);
            // dst >= delta >= dst \ fml0
            // dst \ fml0 == delta & dst & \ fml0
            // dst & delta = delta
            expr_ref fml4(m), fml5(m);
            fml4 = m.mk_and(fml2, m.mk_not(fml0));
            fml5 = m.mk_and(fml3, fml4);
            sub(fml4, vars.size(), vars.c_ptr(), fml4);
            sub(fml5, vars.size(), vars.c_ptr(), fml5);
            check_equiv(fml4, fml5);
            fml4 = m.mk_and(fml3, fml2);
            sub(fml3, vars.size(), vars.c_ptr(), fml3);
            sub(fml4, vars.size(), vars.c_ptr(), fml4);
            check_equiv(fml3, fml4);
        }
    }

    class check_relation_plugin::union_fn : public relation_union_fn {
        scoped_ptr<relation_union_fn> m_union;
    public:
        union_fn(relation_union_fn* m): m_union(m) {}

        virtual void operator()(relation_base & _r, const relation_base & _src, relation_base * _delta) {
            TRACE("doc", _r.display(tout << "dst:\n"); _src.display(tout  << "src:\n"););
            check_relation& r = get(_r);
            check_relation const& src = get(_src);
            check_relation* d = get(_delta);
            expr_ref fml0 = r.m_fml;
            (*m_union)(r.rb(), src.rb(), d?(&d->rb()):0);
            r.get_plugin().verify_union(fml0, src.rb(), r.rb(), d?(&d->rb()):0);
            r.rb().to_formula(r.m_fml);
            if (d) d->rb().to_formula(d->m_fml);
        }
    };
    relation_union_fn * check_relation_plugin::mk_union_fn(
        const relation_base & tgt, const relation_base & src, 
        const relation_base * delta) {
        relation_base const* d1 = delta?(&(get(*delta).rb())):0;
        relation_union_fn* u = m_base->mk_union_fn(get(tgt).rb(), get(src).rb(), d1);
        return u?alloc(union_fn, u):0;
    }
    relation_union_fn * check_relation_plugin::mk_widen_fn(
        const relation_base & tgt, const relation_base & src, 
        const relation_base * delta) {
        relation_base const* d1 = delta?(&(get(*delta).rb())):0;
        relation_union_fn* u = m_base->mk_widen_fn(get(tgt).rb(), get(src).rb(), d1);
        return u?alloc(union_fn, u):0;
    }

    class check_relation_plugin::filter_identical_fn : public relation_mutator_fn {        
        unsigned_vector                 m_cols;
        scoped_ptr<relation_mutator_fn> m_filter;
    public:
        filter_identical_fn(relation_mutator_fn* f, unsigned col_cnt, const unsigned *identical_cols)
            : m_cols(col_cnt, identical_cols),
              m_filter(f) {
        }

        virtual ~filter_identical_fn() {}
        
        virtual void operator()(relation_base & _r) {
            check_relation& r = get(_r);
            check_relation_plugin& p = r.get_plugin();            
            ast_manager& m = p.m;
            expr_ref cond(m);
            relation_signature const& sig = r.get_signature();
            expr_ref_vector conds(m);
            unsigned c1 = m_cols[0];
            for (unsigned i = 1; i < m_cols.size(); ++i) {
                unsigned c2 = m_cols[i];
                conds.push_back(m.mk_eq(m.mk_var(c1, sig[c1]), m.mk_var(c2, sig[c2])));
            }
            cond = mk_and(m, conds.size(), conds.c_ptr());
            r.consistent_formula();
            (*m_filter)(r.rb());
            p.verify_filter(r.m_fml, r.rb(), cond);
            r.rb().to_formula(r.m_fml);
        }
    };
    relation_mutator_fn * check_relation_plugin::mk_filter_identical_fn(
        const relation_base & t, unsigned col_cnt, const unsigned * identical_cols) {
        relation_mutator_fn* r = m_base->mk_filter_identical_fn(get(t).rb(), col_cnt, identical_cols);
        return r?alloc(filter_identical_fn, r, col_cnt, identical_cols):0;
    }

    class check_relation_plugin::filter_interpreted_fn : public relation_mutator_fn {
        scoped_ptr<relation_mutator_fn> m_mutator;
        app_ref m_condition;
    public:
        filter_interpreted_fn(relation_mutator_fn* r, app_ref& condition) :
            m_mutator(r),
            m_condition(condition) {
        }

        virtual ~filter_interpreted_fn() {}
        
        virtual void operator()(relation_base & tb) {            
            check_relation& r = get(tb);
            check_relation_plugin& p = r.get_plugin();            
            expr_ref fml = r.m_fml;
            (*m_mutator)(r.rb());
            p.verify_filter(fml, r.rb(), m_condition);
            r.rb().to_formula(r.m_fml);
        }
    };
    relation_mutator_fn * check_relation_plugin::mk_filter_interpreted_fn(const relation_base & t, app * condition) {
        relation_mutator_fn* r = m_base->mk_filter_interpreted_fn(get(t).rb(), condition);
        app_ref cond(condition, m);
        return r?alloc(filter_interpreted_fn, r, cond):0;
    }

    class check_relation_plugin::project_fn : public convenient_relation_project_fn {
        scoped_ptr<relation_transformer_fn> m_project;
    public:
        project_fn(relation_transformer_fn* p,
                   relation_base const & t, 
                   unsigned removed_col_cnt, const unsigned * removed_cols) 
            : convenient_relation_project_fn(t.get_signature(), removed_col_cnt, removed_cols),
              m_project(p) {
        }

        virtual ~project_fn() {}

        virtual relation_base * operator()(const relation_base & tb) {
            check_relation const& t = get(tb);
            check_relation_plugin& p = t.get_plugin();
            relation_base* r = (*m_project)(t.rb());
            p.verify_project(tb, *r, m_removed_cols);
            return alloc(check_relation, p, r->get_signature(), r);
        }
    };
    

    relation_transformer_fn * check_relation_plugin::mk_project_fn(
        const relation_base & t, unsigned col_cnt, 
        const unsigned * removed_cols) {
        relation_transformer_fn* p = m_base->mk_project_fn(get(t).rb(), col_cnt, removed_cols);
        return p?alloc(project_fn, p, t, col_cnt, removed_cols):0;
    }

    class check_relation_plugin::rename_fn : public convenient_relation_rename_fn {
        scoped_ptr<relation_transformer_fn> m_permute;
    public:
        rename_fn(relation_transformer_fn* permute, 
                  relation_base const& t, unsigned cycle_len, const unsigned * cycle) 
            : convenient_relation_rename_fn(t.get_signature(), cycle_len, cycle),
              m_permute(permute) {
        }

        virtual ~rename_fn() {}

        virtual relation_base * operator()(const relation_base & _t) {
            check_relation const& t = get(_t);
            check_relation_plugin& p = t.get_plugin();            
            relation_signature const& sig = get_result_signature();
            relation_base* r = (*m_permute)(t.rb());         
            p.verify_permutation(t.rb(), *r, m_cycle);
            return alloc(check_relation, p, sig, r);            
        }
    };
    relation_transformer_fn * check_relation_plugin::mk_rename_fn(
        const relation_base & r, 
        unsigned cycle_len, const unsigned * permutation_cycle) {
        relation_transformer_fn* p = m_base->mk_rename_fn(get(r).rb(), cycle_len, permutation_cycle);
        return p?alloc(rename_fn, p, r, cycle_len, permutation_cycle):0;
    }

    class check_relation_plugin::filter_equal_fn : public relation_mutator_fn {
        scoped_ptr<relation_mutator_fn> m_filter;
        relation_element m_val;
        unsigned         m_col;
    public:
        filter_equal_fn(relation_mutator_fn* filter, relation_base const& t, 
                        const relation_element val, unsigned col):
            m_filter(filter), 
            m_val(val),
            m_col(col)
        {}
        virtual ~filter_equal_fn() { }        
        virtual void operator()(relation_base & tb) {
            check_relation & t = get(tb);
            check_relation_plugin& p = t.get_plugin();
            (*m_filter)(t.rb());
            expr_ref fml = t.m_fml;
            t.rb().to_formula(t.m_fml);
            fml = p.m.mk_and(fml, p.m.mk_eq(p.m.mk_var(m_col, t.get_signature()[m_col]), m_val));
            p.check_equiv(t.ground(fml), t.ground(t.m_fml));
        }
    };
    relation_mutator_fn * check_relation_plugin::mk_filter_equal_fn(
        const relation_base & t, const relation_element & value, unsigned col) {
        relation_mutator_fn* r = m_base->mk_filter_equal_fn(get(t).rb(), value, col);
        return r?alloc(filter_equal_fn, r, t, value, col):0;
    }




    class check_relation_plugin::negation_filter_fn : public relation_intersection_filter_fn {
        scoped_ptr<relation_intersection_filter_fn> m_filter;
        const unsigned_vector m_t_cols;
        const unsigned_vector m_neg_cols;
    public:
        negation_filter_fn(
            relation_intersection_filter_fn* filter,
            unsigned joined_col_cnt, const unsigned *t_cols, const unsigned *neg_cols)
            : m_filter(filter), 
              m_t_cols(joined_col_cnt, t_cols), m_neg_cols(joined_col_cnt, neg_cols) {
            SASSERT(joined_col_cnt > 0);
        }
        
        virtual void operator()(relation_base& tb, const relation_base& negb) {
            check_relation& t = get(tb);
            check_relation const& n = get(negb);
            check_relation_plugin& p = t.get_plugin();
            (*m_filter)(t.rb(), n.rb());
            IF_VERBOSE(0, verbose_stream() << "TBD: verify filter_negation\n";);
            t.rb().to_formula(t.m_fml);
        }
    };

    relation_intersection_filter_fn * check_relation_plugin::mk_filter_by_negation_fn(
        const relation_base& t,
        const relation_base& neg, unsigned joined_col_cnt, const unsigned *t_cols,
        const unsigned *negated_cols) {
        relation_intersection_filter_fn* f = mk_filter_by_negation_fn(get(t).rb(), get(neg).rb(), joined_col_cnt, t_cols, negated_cols);
        return f?alloc(negation_filter_fn, f, joined_col_cnt, t_cols, negated_cols):0;
    }


    class check_relation_plugin::filter_proj_fn : public convenient_relation_project_fn {
        app_ref     m_cond;
        scoped_ptr<relation_transformer_fn> m_xform;
    public:
        filter_proj_fn(relation_transformer_fn* xform,
                       relation_base const& t, app_ref& cond,
                       unsigned col_cnt, const unsigned * removed_cols) :
            convenient_relation_project_fn(t.get_signature(), col_cnt, removed_cols),
            m_cond(cond),
            m_xform(xform)
        {}
        
        virtual ~filter_proj_fn() {}

        virtual relation_base* operator()(const relation_base & tb) {
            check_relation const & t = get(tb);
            check_relation_plugin& p = t.get_plugin();
            relation_base* r = (*m_xform)(t.rb());
            p.verify_filter_project(t.rb(), *r, m_cond, m_removed_cols);
            relation_signature const& sig = get_result_signature();
            return alloc(check_relation, p, sig, r);
        }
    };
    relation_transformer_fn * check_relation_plugin::mk_filter_interpreted_and_project_fn(
        const relation_base & t, app * condition,
        unsigned removed_col_cnt, const unsigned * removed_cols) {
        relation_transformer_fn* r = m_base->mk_filter_interpreted_and_project_fn(get(t).rb(), condition, removed_col_cnt, removed_cols);
        app_ref cond(condition, m);
        return r?alloc(filter_proj_fn, r, t, cond, removed_col_cnt, removed_cols):0;
    }




}