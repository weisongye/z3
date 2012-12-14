/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    assertion_stack.cpp

Abstract:
    
    Assertion stacks
    
Author:

    Leonardo de Moura (leonardo) 2012-02-17

Revision History:

--*/
#include"assertion_stack.h"
#include"well_sorted.h"
#include"ast_smt2_pp.h"
#include"ref_util.h"
#include"expr_replacer.h"
#include"model.h"
#include"expr_substitution.h"
#include"for_each_expr.h"
#include"extension_model_converter.h"
#include"filter_model_converter.h"

#define MC_TAG_EXTENSION 0
#define MC_TAG_FILTER    1

struct assertion_stack::imp {
    ast_manager &                m_manager;
    bool                         m_models_enabled;  // model generation is enabled.
    bool                         m_proofs_enabled;  // proof production is enabled. m_manager.proofs_enabled() must be true if m_proofs_enabled == true
    bool                         m_core_enabled;    // unsat core extraction is enabled.
    bool                         m_inconsistent; 
    expr_ref_vector              m_forms;
    proof_ref_vector             m_proofs;
    expr_dependency_ref_vector   m_deps;
    unsigned                     m_forms_qhead; // position of first uncommitted assertion
    unsigned                     m_mc_qhead;

    // Set of declarations that can't be eliminated
    obj_hashtable<func_decl>     m_frozen_set;
    func_decl_ref_vector         m_frozen;
    
    // Limited model converter support, it supports only extensions and filters.
    // It should be viewed as combination of extension_model_converter and 
    // filter_model_converter for goals.
    expr_substitution            m_csubst;  // substitution for eliminated constants

    // Model converter is just two sequences: func_decl and tag.
    // Tag 0 (extension) func_decl was eliminated, and its definition is in m_vsubst or m_fsubst.
    // Tag 1 (filter) func_decl was introduced by tactic, and must be removed from model.
    func_decl_ref_vector         m_mc;      
    char_vector                  m_mc_tag;
    
    struct scope {
        unsigned                 m_forms_lim;
        unsigned                 m_frozen_lim;
        unsigned                 m_mc_lim;
        bool                     m_inconsistent_old;
    };
    
    svector<scope>               m_scopes;

    extension_model_converter *  m_emc; // auxiliary field

    imp(ast_manager & m, bool models_enabled, bool core_enabled):
        m_manager(m),
        m_forms(m),
        m_proofs(m),
        m_deps(m),
        m_frozen(m),
        m_csubst(m, core_enabled),
        m_mc(m) {
        init(m.proofs_enabled(), models_enabled, core_enabled);
    }

    imp(ast_manager & m, bool proofs_enabled, bool models_enabled, bool core_enabled):
        m_manager(m),
        m_forms(m),
        m_proofs(m),
        m_deps(m),
        m_frozen(m),
        m_csubst(m, core_enabled, proofs_enabled),
        m_mc(m) {
        init(proofs_enabled, models_enabled, core_enabled);
    }

    void init(bool proofs_enabled, bool models_enabled, bool core_enabled) {
        m_models_enabled = models_enabled;
        m_proofs_enabled = proofs_enabled;
        m_core_enabled   = core_enabled;
        m_inconsistent   = false;
        m_forms_qhead    = 0;
        m_mc_qhead       = 0;
        m_emc            = 0;
    }

    ~imp() {
    }
    
    ast_manager & m() const { return m_manager; }

    bool models_enabled() const { return m_models_enabled; }

    bool proofs_enabled() const { return m_proofs_enabled; }

    bool unsat_core_enabled() const { return m_core_enabled; }

    bool inconsistent() const { return m_inconsistent; }

    unsigned size() const { return m_forms.size(); }

    unsigned num_exprs() const {
        expr_fast_mark1 visited;
        unsigned sz = size();
        unsigned r  = 0;
        for (unsigned i = 0; i < sz; i++) {
            r += get_num_exprs(form(i), visited);
        }
        return r;
    }

    unsigned qhead() const { return m_forms_qhead; }

    expr * form(unsigned i) const { return m_forms.get(i); }

    proof * pr(unsigned i) const { 
        if (proofs_enabled())
            return m_proofs.get(i);
        else
            return 0;
    }

    expr_dependency * dep(unsigned i) const { 
        if (unsat_core_enabled())
            return m_deps.get(i);
        else
            return 0;
    }

    void expand(expr * f, proof * pr, expr_dependency * dep, expr_ref & new_f, proof_ref & new_pr, expr_dependency_ref & new_dep) {
        if (m_csubst.empty()) {
            new_f   = f;
            new_pr  = pr;
            new_dep = dep;
        }
        else {
            scoped_ptr<expr_replacer> r = mk_default_expr_replacer(m());
            r->set_substitution(&m_csubst);
            (*r)(f, new_f, new_pr, new_dep);
            // new_pr   is a proof for  f == new_f
            // new_dep  are the dependencies for showing f == new_f
            if (proofs_enabled())
                new_pr = m_manager.mk_modus_ponens(pr, new_pr); 
            if (unsat_core_enabled())
                new_dep = m().mk_join(dep, new_dep);
        }
    }
    
    void push_back(expr * f, proof * pr, expr_dependency * d) {
        if (m().is_true(f))
            return;
        if (m().is_false(f)) {
            m_inconsistent = true;
        }
        else {
            SASSERT(!m_inconsistent);
        }
        m_forms.push_back(f);
        if (proofs_enabled())
            m_proofs.push_back(pr);
        if (unsat_core_enabled())
            m_deps.push_back(d);
    }

    void quick_process(bool save_first, expr * & f, expr_dependency * d) {
        if (!m().is_and(f) && !(m().is_not(f) && m().is_or(to_app(f)->get_arg(0)))) {
            if (!save_first)
                push_back(f, 0, d);
            return; 
        }
        typedef std::pair<expr *, bool> expr_pol;
        sbuffer<expr_pol, 64> todo;
        todo.push_back(expr_pol(f, true));
        while (!todo.empty()) {
            if (m_inconsistent)
                return;
            expr_pol p  = todo.back();
            expr * curr = p.first;
            bool   pol  = p.second;
            todo.pop_back();
            if (pol && m().is_and(curr)) {
                app * t = to_app(curr);
                unsigned i = t->get_num_args();
                while (i > 0) {
                    --i;
                    todo.push_back(expr_pol(t->get_arg(i), true));
                }
            }
            else if (!pol && m().is_or(curr)) {
                app * t = to_app(curr);
                unsigned i = t->get_num_args();
                while (i > 0) {
                    --i;
                    todo.push_back(expr_pol(t->get_arg(i), false));
                }
            }
            else if (m().is_not(curr)) {
                todo.push_back(expr_pol(to_app(curr)->get_arg(0), !pol));
            }
            else {
                if (!pol) 
                    curr = m().mk_not(curr);
                if (save_first) {
                    f  = curr;
                    save_first = false;
                }
                else {
                    push_back(curr, 0, d);
                }
            }
        }
    }
    
    void process_and(bool save_first, app * f, proof * pr, expr_dependency * d, expr_ref & out_f, proof_ref & out_pr) {
        unsigned num = f->get_num_args();
        for (unsigned i = 0; i < num; i++) {
            if (m_inconsistent)
                return;
            slow_process(save_first && i == 0, f->get_arg(i), m().mk_and_elim(pr, i), d, out_f, out_pr);
        }
    }
    
    void process_not_or(bool save_first, app * f, proof * pr, expr_dependency * d, expr_ref & out_f, proof_ref & out_pr) {
        unsigned num = f->get_num_args();
        for (unsigned i = 0; i < num; i++) {
            if (m_inconsistent)
                return;
            expr * child = f->get_arg(i);
            if (m().is_not(child)) {
                expr * not_child = to_app(child)->get_arg(0);
                slow_process(save_first && i == 0, not_child, m().mk_not_or_elim(pr, i), d, out_f, out_pr);
            }
            else {
                expr_ref not_child(m());
                not_child = m().mk_not(child);
                slow_process(save_first && i == 0, not_child, m().mk_not_or_elim(pr, i), d, out_f, out_pr);
            }
        }
    }
    
    void slow_process(bool save_first, expr * f, proof * pr, expr_dependency * d, expr_ref & out_f, proof_ref & out_pr) {
        if (m().is_and(f)) 
            process_and(save_first, to_app(f), pr, d, out_f, out_pr);
        else if (m().is_not(f) && m().is_or(to_app(f)->get_arg(0))) 
            process_not_or(save_first, to_app(to_app(f)->get_arg(0)), pr, d, out_f, out_pr);
        else if (save_first) {
            out_f  = f;
            out_pr = pr;
        }
        else {
            push_back(f, pr, d);
        }
    }
    
    void slow_process(expr * f, proof * pr, expr_dependency * d) {
        expr_ref out_f(m());
        proof_ref out_pr(m());
        slow_process(false, f, pr, d, out_f, out_pr);
    }
    
    void assert_expr(expr * f, proof * pr, expr_dependency * d) {
        SASSERT(proofs_enabled() == (pr != 0 && !m().is_undef_proof(pr)));
        if (m_inconsistent)
            return;
        expr_ref new_f(m()); proof_ref new_pr(m()); expr_dependency_ref new_d(m());
        expand(f, pr, d, new_f, new_pr, new_d);
        f = new_f; pr = new_pr; d = new_d;
        if (proofs_enabled())
            slow_process(f, pr, d);
        else
            quick_process(false, f, d);
    }
    
    void update(unsigned i, expr * f, proof * pr, expr_dependency * d) {
        SASSERT(i >= m_forms_qhead);
        SASSERT(proofs_enabled() == (pr != 0 && !m().is_undef_proof(pr)));
        if (m_inconsistent)
            return;
        if (proofs_enabled()) {
            expr_ref out_f(m());
            proof_ref out_pr(m());
            slow_process(true, f, pr, d, out_f, out_pr);
            if (!m_inconsistent) {
                if (m().is_false(out_f)) {
                    push_back(out_f, out_pr, d);
                }
                else {
                    m_forms.set(i, out_f);
                    m_proofs.set(i, out_pr);
                    if (unsat_core_enabled())
                        m_deps.set(i, d);
                }
            }
        }
        else {
            quick_process(true, f, d);
            if (!m_inconsistent) {
                if (m().is_false(f)) {
                    push_back(f, 0, d);
                }
                else {
                    m_forms.set(i, f);
                    if (unsat_core_enabled())
                        m_deps.set(i, d);
                }
            }
        }
    }
    
    void expand_and_update(unsigned i, expr * f, proof * pr, expr_dependency * d) {
        SASSERT(i >= m_forms_qhead);
        SASSERT(proofs_enabled() == (pr != 0 && !m().is_undef_proof(pr)));
        if (m_inconsistent)
            return;
        expr_ref new_f(m()); proof_ref new_pr(m()); expr_dependency_ref new_d(m());
        expand(f, pr, d, new_f, new_pr, new_d);
        update(i, new_f, new_pr, new_d);
    }
    
    void push() {
        commit();
        m_scopes.push_back(scope());
        scope & s            = m_scopes.back();
        s.m_forms_lim        = m_forms.size();
        s.m_frozen_lim       = m_frozen.size();
        s.m_mc_lim           = m_mc.size();
        s.m_inconsistent_old = m_inconsistent;
    }

    void restore_mc(unsigned old_size) {
        unsigned sz  = m_mc.size();
        SASSERT(sz >= old_size);
        for (unsigned i = old_size; i < sz; i++) {
            if (m_mc_tag[i] == MC_TAG_EXTENSION) {
                func_decl * f = m_mc.get(i);
                if (f->get_arity() == 0) {
                    expr_ref c(m().mk_const(f), m());
                    SASSERT(m_csubst.contains(c));
                    m_csubst.erase(c);
                }
                else {
                    // Arity > 0
                    // We don't support macros yet.
                }
            }
        }
        m_mc.shrink(old_size);
        m_mc_tag.shrink(old_size);
        m_mc_qhead = old_size;
    }

    void restore_frozen(unsigned old_size) {
        unsigned sz  = m_frozen.size();
        SASSERT(sz >= old_size);
        for (unsigned i = old_size; i < sz; i++) {
            m_frozen_set.erase(m_frozen.get(i));
        }
        m_frozen.shrink(old_size);
    }

    void restore_forms(unsigned old_size) {
        m_forms.shrink(old_size);
        if (proofs_enabled())
            m_proofs.shrink(old_size);
        if (unsat_core_enabled())
            m_deps.shrink(old_size);
        m_forms_qhead = old_size;
    }

    void pop(unsigned num_scopes) {
        unsigned new_lvl    = m_scopes.size() - num_scopes;
        scope & s           = m_scopes[new_lvl];
        m_inconsistent      = s.m_inconsistent_old;
        restore_frozen(s.m_frozen_lim);
        restore_mc(s.m_mc_lim);
        restore_forms(s.m_forms_lim);
        m_scopes.shrink(new_lvl);
    }

    struct freeze_proc {
        obj_hashtable<func_decl>  &  m_frozen_set;
        func_decl_ref_vector      &  m_frozen; 
        freeze_proc(obj_hashtable<func_decl> & s, func_decl_ref_vector & f):m_frozen_set(s), m_frozen(f) {}
        void operator()(var * n) {}
        void operator()(quantifier * n) {}
        void operator()(app * n) {
            if (is_uninterp(n)) {
                func_decl * f = n->get_decl();
                if (!m_frozen_set.contains(f)) {
                    m_frozen_set.insert(f);
                    m_frozen.push_back(f);
                }
            }
        }
    };

    void commit() {
        expr_fast_mark1 uf_visited; // marks for updating frozen
        freeze_proc p(m_frozen_set, m_frozen);
        unsigned sz = m_forms.size();
        for (unsigned i = m_forms_qhead; i < sz; i++)
            quick_for_each_expr(p, uf_visited, m_forms.get(i));
        sz = m_mc.size();
        for (unsigned i = m_mc_qhead; i < sz; i++) {
            if (m_mc_tag[i] == MC_TAG_EXTENSION) {
                func_decl * f = m_mc.get(i);
                if (f->get_arity() == 0) {
                    expr_ref c(m().mk_const(f), m());
                    expr * def; proof * pr; expr_dependency * dep;
                    VERIFY(m_csubst.find(c, def, pr, dep));
                    quick_for_each_expr(p, uf_visited, def);
                }
                else {
                    // Arity > 0
                    // We don't support macros yet.
                }
            }
        }
        m_forms_qhead = m_forms.size();
        m_mc_qhead    = m_mc.size();
    }

    unsigned scope_lvl() const { 
        return m_scopes.size(); 
    }

    void freeze(func_decl * f) {
        if (m_frozen_set.contains(f))
            return;
        m_frozen_set.insert(f);
        m_frozen.push_back(f);
    }

    bool is_frozen(func_decl * f) const { 
        return m_frozen_set.contains(f); 
    }
    
    void add_filter(func_decl * f) {
        m_mc.push_back(f);
        m_mc_tag.push_back(MC_TAG_FILTER);
    }
    
    void add_definition(app * c, expr * def, proof * pr, expr_dependency * dep) {
        SASSERT(c->get_num_args() == 0);
        SASSERT(!m_csubst.contains(c));
        m_csubst.insert(c, def, pr, dep);
        func_decl * d = c->get_decl();
        m_mc.push_back(d);
        m_mc_tag.push_back(MC_TAG_EXTENSION);
    }

    void set_cancel(bool f) {
        if (m_emc != 0 && f)
            m_emc->cancel();
    }

    void convert(model_ref & md) {
        unsigned top = static_cast<unsigned>(m_mc.size());
        if (top > 0) {
            top--;
            while (true) {
                if (m_mc_tag[top] == MC_TAG_EXTENSION) {
                    extension_model_converter emc(m());
                    #pragma omp critical (assertion_stack)
                    {
                        m_emc = &emc;
                    }
                    while (true) {
                        SASSERT(m_mc_tag[top] == MC_TAG_EXTENSION);
                        func_decl * f = m_mc.get(top);
                        if (f->get_arity() == 0) {
                            expr_ref c(m().mk_const(f), m());
                            expr * def; proof * pr; expr_dependency * dep;
                            VERIFY(m_csubst.find(c, def, pr, dep));
                            emc.insert(f, def);
                        }
                        else {
                            // arity > 0
                            // we don't support macros yet
                        }
                        if (top == 0)
                            break;
                        top--;
                        if (m_mc_tag[top] != MC_TAG_EXTENSION)
                            break;
                    }
                    emc(md, 0);
                    #pragma omp critical (assertion_stack)
                    {
                        m_emc = 0;
                    }
                }
                else {
                    SASSERT(m_mc_tag[top] == MC_TAG_FILTER);
                    filter_model_converter fm(m());
                    while (true) {
                        SASSERT(m_mc_tag[top] == MC_TAG_FILTER);
                        func_decl * f = m_mc.get(top);
                        fm.insert(f);
                        if (top == 0)
                            break;
                        top--;
                        if (m_mc_tag[top] != MC_TAG_FILTER)
                            break;
                    }
                    fm(md, 0);
                }
                if (top == 0)
                    return;
            }
        }
    }
    
    void display(std::ostream & out, char const * header) const {
        out << "(" << header;
        unsigned sz = size();
        for (unsigned i = 0; i < sz; i++) {
            out << "\n  ";
            if (i == m_forms_qhead) 
                out << "==>\n";
            out << mk_ismt2_pp(form(i), m(), 2);
        }
        out << ")" << std::endl;
    }

    bool is_well_sorted() const {
        unsigned sz = size();
        for (unsigned i = 0; i < sz; i++) {
            expr * t = form(i);
            if (!::is_well_sorted(m(), t))
                return false;
        }
        return true;
    }

    void shrink(unsigned j) {
        SASSERT(j >= m_forms_qhead);
        m_forms.shrink(j);
        if (proofs_enabled())
            m_proofs.shrink(j);
        if (unsat_core_enabled())
            m_deps.shrink(j);
    }

    /**
       \brief Return the position of formula f in the assertion stack
       Return UINT_MAX if f is not in the goal
    */
    unsigned get_idx(expr * f) const {
        unsigned sz = size();
        for (unsigned j = 0; j < sz; j++) {
            if (form(j) == f)
                return j;
        }
        return UINT_MAX;
    }

    /**
       \brief Return the position of formula (not f) in the goal.
       Return UINT_MAX if (not f) is not in the goal
    */
    unsigned get_not_idx(expr * f) const {
        expr * atom;
        unsigned sz = size();
        for (unsigned j = 0; j < sz; j++) {
            if (m().is_not(form(j), atom) && atom == f)
                return j;
        }
        return UINT_MAX;
    }

    void elim_true() {
        if (inconsistent())
            return;
        unsigned sz = size();
        unsigned j  = m_forms_qhead;
        for (unsigned i = m_forms_qhead; i < sz; i++) {
            expr * f = form(i);
            if (m().is_true(f))
                continue;
            if (i == j) {
                j++;
                continue;
            }
            m_forms.set(j, f);
            if (proofs_enabled())
                m_proofs.set(j, pr(i));
            if (unsat_core_enabled())
                m_deps.set(j, dep(i));
            j++;
        }
        shrink(j);
    }
    
    void elim_redundancies(bool use_before_qhead) {
        if (inconsistent())
            return;
        expr_ref_fast_mark1 neg_lits(m());
        expr_ref_fast_mark2 pos_lits(m());
        if (use_before_qhead) {
            // mark expressions occurring before the qhead
            for (unsigned i = 0; i < m_forms_qhead; i++) {
                expr * f = form(i);
                if (m().is_not(f)) {
                    expr * atom = to_app(f)->get_arg(0);
                    neg_lits.mark(atom);
                }
                else {
                    pos_lits.mark(f);
                }
            }
        }
        unsigned sz = size();
        unsigned j  = m_forms_qhead;
        for (unsigned i = m_forms_qhead; i < sz; i++) {
            expr * f = form(i);
            if (m().is_true(f))
                continue;
            if (m().is_not(f)) {
                expr * atom = to_app(f)->get_arg(0);
                if (neg_lits.is_marked(atom))
                    continue;
                if (pos_lits.is_marked(atom)) {
                    proof * p = 0;
                    if (proofs_enabled()) {
                        proof * prs[2] = { pr(get_idx(atom)), pr(i) };
                        p = m().mk_unit_resolution(2, prs);
                    }
                    expr_dependency_ref d(m());
                    if (unsat_core_enabled())
                        d = m().mk_join(dep(get_idx(atom)), dep(i));
                    push_back(m().mk_false(), p, d);                    
                    return;
                }
                neg_lits.mark(atom);
            }
            else {
                if (pos_lits.is_marked(f))
                    continue;
                if (neg_lits.is_marked(f)) {
                    proof * p = 0;
                    if (proofs_enabled()) {
                        proof * prs[2] = { pr(get_not_idx(f)), pr(i) };
                        p = m().mk_unit_resolution(2, prs);
                    }
                    expr_dependency_ref d(m());
                    if (unsat_core_enabled())
                        d = m().mk_join(dep(get_not_idx(f)), dep(i));
                    push_back(m().mk_false(), p, d);
                    return;
                }
                pos_lits.mark(f);
            }
            if (i == j) {
                j++;
                continue;
            }
            m_forms.set(j, f);
            if (proofs_enabled())
                m_proofs.set(j, pr(i));
            if (unsat_core_enabled())
                m_deps.set(j, dep(i));
            j++;
        }
        shrink(j);
    }

};

assertion_stack::assertion_stack(ast_manager & m, bool models_enabled, bool core_enabled) {
    m_imp = alloc(imp, m, models_enabled, core_enabled);
}

assertion_stack::assertion_stack(ast_manager & m, bool proofs_enabled, bool models_enabled, bool core_enabled) {
    m_imp = alloc(imp, m, proofs_enabled, models_enabled, core_enabled);
}

assertion_stack::~assertion_stack() {
    dealloc(m_imp);
}

void assertion_stack::reset() {
    ast_manager & m     = m_imp->m_manager;
    bool models_enabled = m_imp->m_models_enabled;
    bool proofs_enabled = m_imp->m_proofs_enabled;
    bool core_enabled   = m_imp->m_core_enabled;
    #pragma omp critical (assertion_stack)
    {
        dealloc(m_imp);
        m_imp = alloc(imp, m, proofs_enabled, models_enabled, core_enabled);
    }
}

ast_manager & assertion_stack::m() const { 
    return m_imp->m(); 
}

bool assertion_stack::models_enabled() const { 
    return m_imp->models_enabled();
}

bool assertion_stack::proofs_enabled() const { 
    return m_imp->proofs_enabled(); 
}

bool assertion_stack::unsat_core_enabled() const { 
    return m_imp->unsat_core_enabled(); 
}

bool assertion_stack::inconsistent() const { 
    return m_imp->inconsistent(); 
}

unsigned assertion_stack::size() const { 
    return m_imp->size();
}

unsigned assertion_stack::num_exprs() const { 
    return m_imp->num_exprs();
}

unsigned assertion_stack::qhead() const { 
    return m_imp->qhead();
}

expr * assertion_stack::form(unsigned i) const { 
    return m_imp->form(i);
}

proof * assertion_stack::pr(unsigned i) const { 
    return m_imp->pr(i);
}

expr_dependency * assertion_stack::dep(unsigned i) const { 
    return m_imp->dep(i);
}

void assertion_stack::assert_expr(expr * f, proof * pr, expr_dependency * d) {
    return m_imp->assert_expr(f, pr, d);
}

void assertion_stack::assert_expr(expr * f) {
    assert_expr(f, proofs_enabled() ? m().mk_asserted(f) : 0, 0);
}

void assertion_stack::reset_after_qhead() {
    m_imp->shrink(qhead());
}
        
void assertion_stack::update(unsigned i, expr * f, proof * pr, expr_dependency * d) {
    m_imp->update(i, f, pr, d);
}

void assertion_stack::expand_and_update(unsigned i, expr * f, proof * pr, expr_dependency * d) {
    m_imp->expand_and_update(i, f, pr, d);
}

void assertion_stack::commit() {
    m_imp->commit();
}

void assertion_stack::push() {
    m_imp->push();
}

void assertion_stack::pop(unsigned num_scopes) {
    m_imp->pop(num_scopes);
}

unsigned assertion_stack::scope_lvl() const {
    return m_imp->scope_lvl();
}
  
bool assertion_stack::is_well_sorted() const {
    return m_imp->is_well_sorted();
}

void assertion_stack::freeze(func_decl * f) {
    m_imp->freeze(f);
}

bool assertion_stack::is_frozen(func_decl * f) const {
    return m_imp->is_frozen(f);
}

void assertion_stack::add_filter(func_decl * f) {
    m_imp->add_filter(f);
}

void assertion_stack::add_definition(app * c, expr * def, proof * pr, expr_dependency * dep) {
    m_imp->add_definition(c, def, pr, dep);
}

void assertion_stack::convert(model_ref & m) {
    m_imp->convert(m);
}

void assertion_stack::display(std::ostream & out, char const * header) const {
    m_imp->display(out, header);
}

void assertion_stack::set_cancel(bool f) {
    #pragma omp critical (assertion_stack)
    {
        m_imp->set_cancel(f);
    }
}

void assertion_stack::elim_true() {
    m_imp->elim_true();
}

void assertion_stack::elim_redundancies(bool use_before_qhead) {
    m_imp->elim_redundancies(use_before_qhead);
}

