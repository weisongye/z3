/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_kernel.cpp

Abstract:

    MCSAT kernel

Author:

    Leonardo de Moura (leonardo) 2012-11-01.

Revision History:

--*/
#include"mcsat_kernel.h"
#include"statistics.h"
#include"mcsat_expr_manager.h"
#include"mcsat_node_manager.h"
#include"mcsat_value_manager.h"
#include"mcsat_node_attribute.h"
#include"mcsat_clause.h"
#include"mcsat_exception.h"
#include"mcsat_plugin.h"
#include"ast_util.h"

namespace mcsat {

    struct kernel::imp {
        typedef std::pair<expr *, proof *> expr_proof_pair;
        typedef svector<expr_proof_pair>   expr_proof_pair_vector;
        typedef svector<node>              node_queue;
        typedef svector<char>              node2value;     
        typedef trail_vector               node2justification;

        bool                      m_fresh;
        bool                      m_proofs_enabled;
        expr_manager              m_expr_manager;
        node_manager              m_node_manager;
        node_attribute_manager    m_attribute_manager;
        value_manager             m_value_manager;
        trail_manager             m_trail_manager;
        small_object_allocator    m_allocator;
        id_gen                    m_cls_id_gen;
        clause_vector             m_clauses;
        clause_vector             m_lemmas;
        vector<clause_vector>     m_lemmas_to_reinit;
        plugin_ref_vector         m_plugins;
        trail_stack               m_trail_stack;
        // Boolean node assignment and justification
        node2value                m_node2value;
        node2justification        m_node2justification;
        // 
        node_queue                m_to_internalize; // internalization todo queue.
        expr_proof_pair_vector    m_new_axioms;     // auxiliary axioms created by plugins.
        basic_recognizers         m_butil;
        unsigned                  m_search_lvl;
        struct scope {
            unsigned              m_clauses_lim;
            bool                  m_inconsistent;
        };
        struct base_scope {
            unsigned              m_lemmas_lim;
        };
        svector<scope>            m_scopes;
        svector<base_scope>       m_base_scopes; // for user defined backtracking points

        // conflict
        propagated_literal *      m_conflict_l;
        trail *                   m_conflict_not_l;
        
        // auxiliary fields
        ptr_vector<expr>          m_saved_atoms;
        clause_vector             m_saved_clauses;
        // auxiliary fields for conflict resolution
        literal_vector            m_literal_antecedents;
        trail_vector              m_trail_antecedents;
        ts_expr_ref_vector        m_new_antecedents;
        model_decision_vector     m_decisions;
        
        literal_vector            m_lemma_literals;
        ts_expr_ref_vector        m_lemma_new_literals;
        

        volatile bool             m_cancel;

        void checkpoint() {
            // TODO
        }

        bool inconsistent() const {
            return m_conflict_l != 0;
        }

        void add_axiom(expr * ax, proof_ref & pr) {
            m_new_axioms.push_back(expr_proof_pair(ax, pr));
        }

        lbool get_value(node n) const {
            return static_cast<lbool>(m_node2value[n.index()]);
        }

        lbool get_value(literal l) const {
            lbool r = get_value(l.var());
            return l.sign() ? ~r : r;
        }

        trail * get_justification(node n) const {
            SASSERT(get_value(n) != l_undef);
            return m_node2justification[n.index()];
        }

        void assign_literal(literal l, trail * t) {
            SASSERT(get_value(l) == l_undef);
            unsigned p_idx              = l.var().index();
            m_node2value[p_idx]         = l.sign() ? l_false : l_true;
            m_node2justification[p_idx] = t;
        }
        
        void add_propagation(propagation * p) {
            if (!inconsistent()) {
                literal l = p->lit();
                if (l != null_literal) {
                    lbool l_value = get_value(l);
                    if (l_value == l_true) {
                        // redundant
                        return; 
                    }
                    else if (l_value == l_false) {
                        // conflict
                        m_conflict_l     = static_cast<propagated_literal*>(p);
                        m_conflict_not_l = get_justification(l.var());
                    }
                    else {
                        assign_literal(l, p);
                    }
                }
                m_trail_stack.push_back(p);
            }
        }

        node mk_new_node(expr * n) {
            SASSERT(!m_node_manager.contains(n));
            node r = m_node_manager.mk_node(n);
            unsigned r_idx = r.index();
            m_node2value.reserve(r_idx+1);
            m_node2justification.reserve(r_idx+1);
            m_node2value[r_idx]         = l_undef;
            m_node2justification[r_idx] = 0;
            SASSERT(m_node_manager.contains(n));
            return r;
        }
        
        node mk_node(expr * n) {
            if (m_node_manager.contains(n))
                return m_node_manager.mk_node(n);
            else
                return mk_new_node(n);
        }

        class init_ctx : public initialization_context {
            imp & m;
        public:
            init_ctx(imp & _m):m(_m) {}
            virtual bool proofs_enabled() const { return m.m_proofs_enabled; }
            virtual family_id get_family_id(char const * n) { return m.m_expr_manager.get_family_id(n); }
            virtual node_uint_attribute &   mk_uint_attribute() { return m.m_attribute_manager.mk_uint_attribute(); }
            virtual node_double_attribute & mk_double_attribute() { return m.m_attribute_manager.mk_double_attribute(); }
            virtual trail_kind mk_trail_kind() { return m.m_trail_manager.mk_kind(); }
        };

        class internalization_ctx : public internalization_context {
            imp &                    m;
        public:
            internalization_ctx(imp & _m):m(_m) {}
            
            virtual expr_manager & em() { 
                return m.m_expr_manager;
            }

            virtual expr * to_expr(node n) { 
                return m.m_node_manager.to_expr(n);
            }

            virtual node mk_node(expr * n) { 
                return m.mk_node(n);
            }
            
            virtual void add_axiom(expr * ax, proof_ref & pr) {
                m.add_axiom(ax, pr);
            }

            virtual trail_manager & tm() {
                return m.m_trail_manager;
            }

            virtual void add_propagation(propagation * p) {
                m.add_propagation(p);
            }

            virtual clause * mk_clause(unsigned sz, literal const * lits, proof * pr) {
                return m.mk_aux_clause(sz, lits, pr);
            }
        };

        class propagation_ctx : public propagation_context {
            imp &    m;
            unsigned m_pidx;
        public:
            propagation_ctx(imp & _m, unsigned pidx):m(_m), m_pidx(pidx) {}

            virtual trail_manager & tm() {
                return m.m_trail_manager;
            }

            virtual trail * next() {
                return m.m_trail_stack.next(m_pidx);
            }

            virtual void add_propagation(propagation * p) {
                m.add_propagation(p);
            }

            virtual void add_axiom(expr * ax, proof_ref & pr) {
                m.add_axiom(ax, pr);
            }
        };

        imp(ast_manager & m, bool proofs_enabled):
            m_expr_manager(m),
            m_attribute_manager(m_node_manager),
            m_allocator("mcsat_kernel"),
            m_butil(m.get_basic_family_id()),
            m_new_antecedents(m_expr_manager),
            m_lemma_new_literals(m_expr_manager) {
            m_proofs_enabled = proofs_enabled;
            m_search_lvl     = 0;
            m_conflict_l     = 0;
            m_conflict_not_l = 0;
            m_fresh          = true;
            m_cancel         = false;
        }
	
	~imp() {
	}

        // Return true if the kernel is "fresh" and assertions were not added yet.
        bool is_fresh() const {
            return m_fresh;
        }

        expr * lit2expr(literal l) {
            expr * atom = m_node_manager.to_expr(l.var());
            if (l.sign())
                return m_expr_manager.mk_app(m_expr_manager.get_basic_family_id(), OP_NOT, atom);
            else
                return atom;
        }

        void add_plugin(plugin * p) {
            init_ctx ctx(*this);
            SASSERT(is_fresh());
            p = p->clone();
            m_plugins.push_back(p);
            p->init(ctx);
        }

        unsigned num_plugins() const {
            return m_plugins.size();
        }

        plugin & p(unsigned i) const {
            return *(m_plugins.get(i));
        }

        unsigned scope_lvl() const {
            return m_scopes.size();
        }

        unsigned base_lvl() const {
            return m_base_scopes.size();
        }

        bool at_base_lvl() const {
            return scope_lvl() == base_lvl(); 
        }

        // -----------------------------------
        //
        // Clauses
        //
        // -----------------------------------

        // Dettach clause from plugins
        void dettach_clause(clause * c) {
            for (unsigned i = 0; i < num_plugins(); i++) {
                p(i).dettach_clause(c);
            }
        }

        void del_clause(clause * c) {
            dettach_clause(c);
            // decrement reference counters 
            unsigned sz = c->size();
            for (unsigned i = 0; i < sz; i++) {
                node p   = (*c)[i].var();
                expr * t = m_node_manager.to_expr(p);
                m_expr_manager.dec_ref(t);
            }
            m_expr_manager.dec_ref(c->pr());
            // recycle id and delete
            m_cls_id_gen.recycle(c->id());
            size_t obj_sz = clause::get_obj_size(sz);
            c->~clause();
            m_allocator.deallocate(obj_sz, c);
        }

        // Let lvl(n) be the scope level where node n was created.
        // Then, this method returns maximum level of the nodes (atoms) in the given clause.
        unsigned get_max_node_lvl(clause const & c) {
            unsigned sz  = c.size();
            unsigned max = 0;
            for (unsigned i = 0; i < sz; i++) {
                node n = c[i].var();
                unsigned lvl = m_node_manager.get_mk_level(n);
                if (lvl > max) 
                    max = lvl;
            }
            return max;
        }

        // Add clause to the appropriate collection.
        //   - Main and auxiliary clauses go to m_clauses
        //   - Lemmas that contains nodes that need to be reinitialized go to m_lemmas_to_reinit
        //   - Lemmas that do not contain nodes that need to be reinitialized go to m_lemmas
        void push_clause(clause * c) {
            if (c->is_lemma()) {
                unsigned lvl = get_max_node_lvl(*c);
                if (lvl > base_lvl()) {
                    m_lemmas_to_reinit.reserve(lvl+1);
                    m_lemmas_to_reinit[lvl].push_back(c);
                }
                else {
                    m_lemmas.push_back(c);
                }
            }
            else {
                m_clauses.push_back(c);
            }
        }

        clause * mk_clause(unsigned sz, literal const * lits, clause::kind k, proof * pr) {
            unsigned id = m_cls_id_gen.mk();
            size_t obj_sz = clause::get_obj_size(sz);
            void * mem;
            mem = m_allocator.allocate(obj_sz);
            clause * c = new (mem) clause(id, sz, lits, k, pr);
            // increase reference counters
            for (unsigned i = 0; i < sz; i++) {
                node p   = lits[i].var();
                expr * t = m_node_manager.to_expr(p);
                m_expr_manager.inc_ref(t);
            }
            m_expr_manager.inc_ref(pr);
            push_clause(c);
            return c;
        }

        clause * mk_aux_clause(unsigned sz, literal const * lits, proof * pr) {
            return mk_clause(sz, lits, clause::AUX, pr);
        }

        clause * mk_lemma(unsigned sz, literal const * lits, proof * pr) {
            return mk_clause(sz, lits, clause::LEMMA, pr);
        }

        // -----------------------------------
        //
        // Internalization
        //
        // -----------------------------------

        void internalize_core(node n) {
            // node was not internalized yet.
            internalization_ctx ctx(*this);
            for (unsigned i = 0; i < num_plugins(); i++) {
                if (p(i).internalize(n, ctx))
                    return;
            }
            throw exception("MCSat could not handle the problem: none of existing plugins could process one of the expressions");
        }

        node internalize(expr * n) {
            SASSERT(m_to_internalize.empty());
            if (m_node_manager.contains(n)) {
                return m_node_manager.mk_node(n);
            }
            else {
                node r = mk_new_node(n);
                internalize_core(r);
                while (!m_to_internalize.empty()) {
                    node n = m_to_internalize.back();
                    m_to_internalize.pop_back();
                    internalize_core(n);
                }
                return r;
            }
        }

        literal internalize_literal(expr * n) {
            expr * atom;
            if (m_butil.is_not(n, atom)) {
                SASSERT(!m_butil.is_not(atom));
                return literal(internalize(atom), true);
            }
            else {
                return literal(internalize(n), false);
            }
        }

        void internalize_clause(clause * c, internalization_ctx & ctx) {
            for (unsigned i = 0; i < num_plugins(); i++) {
                if (p(i).internalize(c, ctx))
                    return; // found plugin to process the clause
            }
            throw exception("MCSat could not handle the problem: none of existing plugins could process one of the input clauses");
        }

        void assert_expr_core(expr * f, proof * pr, bool main) {
            internalization_ctx ctx(*this);
            unsigned num_lits;
            expr * const * lits;
            if (m_butil.is_or(f)) {
                lits     = to_app(f)->get_args();
                num_lits = to_app(f)->get_num_args();
            }
            else {
                lits     = &f;
                num_lits = 1;
            }
            literal_vector new_lits;
            for (unsigned i = 0; i < num_lits; i++) {
                literal l = internalize_literal(lits[i]);
                new_lits.push_back(l);
            }
            clause * c = mk_clause(new_lits.size(), new_lits.c_ptr(), main ? clause::MAIN : clause::AUX, pr);
            internalize_clause(c, ctx);
        }
        
        void assert_expr(expr * f, proof * pr) {
            m_fresh = false;
            SASSERT(m_to_internalize.empty());
            assert_expr_core(f, pr, true);
            while (!m_new_axioms.empty()) {
                expr_proof_pair p = m_new_axioms.back();
                m_new_axioms.pop_back();
                assert_expr_core(p.first, p.second, false);
            }
        }

        // -----------------------------------
        //
        // Cleanup using pop()/push() idiom
        //
        // -----------------------------------

        // Auxiliary method for cleanup.
        // The nodes representing the atoms may be deleted during the cleanup. 
        // Thus, we save the associated expressions
        void save_clause_atoms(clause * c, ptr_vector<expr> & saved_atoms) {
            unsigned sz = c->size();
            for (unsigned i = 0; i < sz; i++) {
                node p   = (*c)[i].var();
                expr * t = m_node_manager.to_expr(p);
                saved_atoms.push_back(t);
            }
        }

        // Auxiliary method for cleanup.
        // See save_clause_atoms.
        void restore_clause_atoms(clause * c, internalization_ctx & ctx, unsigned & head, ptr_vector<expr> & saved_atoms) {
            unsigned sz = c->size();
            for (unsigned i = 0; i < sz; i++, head++) {
                expr * t      = saved_atoms[head];
                node p        = internalize(t);
                literal old_l = (*c)[i];
                (*c)[i]       = literal(p, old_l.sign()); // update literal
            }
            internalize_clause(c, ctx);
        }

        void restore_clauses(clause_vector & saved_clauses, ptr_vector<expr> & saved_atoms) {
            internalization_ctx ctx(*this);
            unsigned ahead = 0; // head for saved_atoms
            unsigned sz = saved_clauses.size();
            for (unsigned i = 0; i < sz; i++) {
                clause * c = saved_clauses[i];
                SASSERT(c->is_main() || c->is_lemma());
                restore_clause_atoms(c, ctx, ahead, saved_atoms);
                push_clause(c);
            }
        }
        
        // Cleanup routine can only be performed at base level, and the level should be greater than 0.
        // This method will probably create many opportunities for propagation.
        void cleanup() {
            SASSERT(at_base_lvl());
            SASSERT(!m_scopes.empty());
            // Since we are in a base level, m_lemmas_to_reinit does not contain any clauses.
            ptr_vector<clause> & saved_clauses = m_saved_clauses; m_saved_clauses.reset(); // main and lemmas that should be saved.
            ptr_vector<expr>   & saved_atoms   = m_saved_atoms;   m_saved_atoms.reset();
            // Save main clauses
            unsigned cls_begin = m_scopes.empty() ? 0 : m_scopes.back().m_clauses_lim;
            unsigned cls_end   = m_clauses.size();
            unsigned j         = cls_begin;
            for (unsigned i = cls_begin; i < cls_end; i++) {
                if (m_clauses[i]->is_main()) {
                    saved_clauses.push_back(m_clauses[i]);
                    dettach_clause(m_clauses[i]);
                    save_clause_atoms(m_clauses[i], saved_atoms);
                }
                else {
                    m_clauses[j] = m_clauses[i];
                    j++;
                }
            }
            m_clauses.shrink(j);
            // Save lemmas
            unsigned lemmas_begin = m_base_scopes.empty() ? 0 : m_base_scopes.back().m_lemmas_lim;
            unsigned lemmas_end   = m_lemmas.size();
            SASSERT(lemmas_end >= lemmas_begin);
            for (unsigned i = lemmas_begin; i < lemmas_end; i++) {
                saved_clauses.push_back(m_lemmas[i]);
                dettach_clause(m_clauses[i]);
                save_clause_atoms(m_lemmas[i], saved_atoms);
            }
            m_lemmas.shrink(lemmas_begin);
            // Cleanup 
            pop(1, true);
            // Restore 
            push(true);
            restore_clauses(saved_clauses, saved_atoms);
        }
        
        // -----------------------------------
        //
        // Backtracking & conflict resolution
        //
        // -----------------------------------

        void push(bool user) {
            SASSERT(m_new_axioms.empty());
            SASSERT(m_to_internalize.empty());
            SASSERT(user || m_scopes.size() == m_base_scopes.size());
            SASSERT(m_scopes.size() >= m_base_scopes.size());
            m_expr_manager.push();
            m_node_manager.push();
            m_value_manager.push();
            m_trail_manager.push();
            m_scopes.push_back(scope());
            scope & s = m_scopes.back();
            s.m_clauses_lim  = m_clauses.size();
            s.m_inconsistent = m_conflict_l != 0;
            if (user) {
                m_base_scopes.push_back(base_scope());
                base_scope & bs = m_base_scopes.back();
                bs.m_lemmas_lim = m_lemmas.size();
            }
            m_trail_stack.push();
            unsigned sz = m_plugins.size();
            for (unsigned i = 0; i < sz; i++) {
                m_plugins.get(i)->push();
            }
        }

        void del_clauses(clause_vector & cs, unsigned old_sz) {
            unsigned sz = cs.size();
            SASSERT(old_sz <= sz);
            for (unsigned i = old_sz; i < sz; i++) {
                clause * c = cs[i];
                del_clause(c);
            }
            cs.shrink(old_sz);
        }

        // Store in saved_clauses the lemmas that need to be reinitialized.
        // Store in saved_atoms the atoms occuring in these clauses.
        void save_lemmas_to_reinit(unsigned new_lvl, clause_vector & saved_clauses, ptr_vector<expr> & saved_atoms) {
            saved_atoms.reset();
            saved_clauses.reset();
            unsigned sz = m_lemmas_to_reinit.size();
            if (sz > new_lvl) {
                for (unsigned i = new_lvl; i < sz; i++) {
                    clause_vector const & cs = m_lemmas_to_reinit[i];
                    unsigned cs_sz = cs.size();
                    for (unsigned j = 0; j < cs_sz; j++) {
                        clause * c = cs[j];
                        saved_clauses.push_back(c);
                        dettach_clause(c);
                        save_clause_atoms(c, saved_atoms);
                    }
                }
                m_lemmas_to_reinit.shrink(new_lvl);
            }
        }

        void reinit_lemmas(clause_vector & saved_clauses, ptr_vector<expr> & saved_atoms) {
            restore_clauses(saved_clauses, saved_atoms);
        }

        void reset_inconsistent() {
            m_conflict_l     = 0;
            m_conflict_not_l = 0;
            // In the future, we should also reset unsat core, proof, etc.
        }

        void restore_assignment(unsigned new_lvl) {
            unsigned i = m_trail_stack.size();
            unsigned begin = m_trail_stack.end_lvl(new_lvl);
            while (i > begin) {
                --i;
                trail * t = m_trail_stack[i];
                literal l = t->lit();
                if (l != null_literal) {
                    unsigned p_idx = l.var().index();
                    SASSERT(m_node2value[p_idx] != l_undef);
                    m_node2value[p_idx]         = l_undef;
                    m_node2justification[p_idx] = 0;
                }
            }
        }

        void pop(unsigned num_scopes, bool user) {
            unsigned sz = m_plugins.size();
            for (unsigned i = 0; i < sz; i++) {
                m_plugins.get(i)->pop(num_scopes);
            }
            SASSERT(user || m_scopes.size() == m_base_scopes.size());
            SASSERT(m_scopes.size() >= m_base_scopes.size());
            SASSERT(num_scopes <= m_scopes.size());
            unsigned new_lvl    = m_scopes.size() - num_scopes;
            restore_assignment(new_lvl);
            m_trail_stack.pop(num_scopes);
            save_lemmas_to_reinit(new_lvl, m_saved_clauses, m_saved_atoms);
            SASSERT(m_lemmas_to_reinit.size() <= new_lvl);
            scope & s           = m_scopes[new_lvl];
            del_clauses(m_clauses, s.m_clauses_lim);
            if (!s.m_inconsistent && inconsistent()) {
                reset_inconsistent();
            }
            m_scopes.shrink(new_lvl);
            if (user) {
                SASSERT(m_saved_clauses.empty()); // we do not have to reinit clauses when backtracking user scopes.
                SASSERT(num_scopes <= m_base_scopes.size());
                unsigned new_lvl    = m_base_scopes.size() - num_scopes;
                base_scope & bs     = m_base_scopes[new_lvl];
                del_clauses(m_clauses, bs.m_lemmas_lim);
                m_base_scopes.shrink(new_lvl);
            }
            m_trail_manager.pop(num_scopes);
            m_value_manager.pop(num_scopes);
            m_node_manager.pop(num_scopes);
            m_expr_manager.pop(num_scopes);
            reinit_lemmas(m_saved_clauses, m_saved_atoms);
            propagate();
        }

        struct em_functor : public expr_manager::functor {
            imp & m_kernel;

            em_functor(imp & k):m_kernel(k) {}
            
            expr * lit2expr(ast_manager & m, literal l) const {
                expr * atom = m_kernel.m_node_manager.to_expr(l.var());
                if (l.sign())
                    return m.mk_not(atom);
                else
                    return atom;
            }
            
            expr * consequent2expr(ast_manager & m, trail * t) const {
                literal l = t->lit();
                if (l == null_literal) {
                    expr * c = t->as_expr(m, to_expr_functor(m_kernel.m_node_manager));
                    SASSERT(c);
                    return c;
                }
                else {
                    return lit2expr(m, l);
                }
            }
        };

        // Create a theory lemma for a propagation.
        // The functor assumes that m_literal_antecedents, m_trail_antecedents, and m_new_antecedents contain the
        // antecedents for the consequent of the propagation.
        struct propagation2th_lemma : public em_functor {
            propagation *  m_propagation;
            ts_proof_ref & m_pr;

            propagation2th_lemma(imp & k, propagation * p, ts_proof_ref & pr):em_functor(k), m_propagation(p), m_pr(pr) {}
            
            virtual void operator()(ast_manager & m, expr_manager::store_expr_functor & to_save) {
                expr_ref_buffer pr_lits(m);
                pr_lits.push_back(consequent2expr(m, m_propagation));
                for (unsigned i = 0; i < m_kernel.m_literal_antecedents.size(); i++) {
                    literal l = m_kernel.m_literal_antecedents[i];
                    pr_lits.push_back(lit2expr(m, ~l));
                }
                expr_ref aux(m);
                for (unsigned i = 0; i < m_kernel.m_trail_antecedents.size(); i++) {
                    trail * t = m_kernel.m_trail_antecedents[i];
                    aux = consequent2expr(m, t);
                    pr_lits.push_back(mk_not(m, aux));
                }
                for (unsigned i = 0; i < m_kernel.m_new_antecedents.size(); i++) {
                    expr * l = m_kernel.m_new_antecedents.get(i);
                    pr_lits.push_back(mk_not(m, l));
                }
                m_pr = m.mk_th_lemma(m_propagation->get_family_id(m), mk_or(m, pr_lits.size(), pr_lits.c_ptr()), 0, 0);
            }

            virtual void set_cancel(bool f) {}
        };


        void process_antecedent(propagation * p, ts_proof_ref & pr) {
            m_literal_antecedents.reset();
            m_trail_antecedents.reset();
            m_new_antecedents.reset();
            m_decisions.reset();

            p->explain(m_expr_manager, m_literal_antecedents, m_trail_antecedents, m_new_antecedents, m_decisions, pr);
            if (m_proofs_enabled && !pr) {
                propagation2th_lemma proc(*this, p, pr);
                m_expr_manager.apply(proc);
            }
            // TODO
        }


        // 
        bool resolve() {
            SASSERT(inconsistent());
            SASSERT(m_conflict_l);
            SASSERT(m_conflict_not_l);
            
            unsigned i = m_trail_stack.size();
            SASSERT(i > 0);

            
            return false;
        }

        // -----------------------------------
        //
        // Propagation
        //
        // -----------------------------------
        
        void propagate() {
            while (true) {
                for (unsigned i = 0; i < num_plugins(); i++) {
                    if (inconsistent())
                        return;
                    checkpoint();
                    propagation_ctx ctx(*this, i);
                    p(i).propagate(ctx);
                }
                if (m_trail_stack.fully_propagated())
                    return;
            }
        }

        // -----------------------------------
        //
        // Search
        //
        // -----------------------------------

        lbool check_sat(unsigned num_assumptions, expr * const * assumptions) {
            if (is_fresh()) 
                return l_true;
            // TODO
            return l_undef;
        }

        void collect_statistics(statistics & st) const {
            // TODO
        }

        void get_unsat_core(ptr_vector<expr> & r) {
            // TODO
        }

        struct mk_model : public expr_manager::functor {
            model_ref & m_model;
            mk_model(model_ref & m):m_model(m) {}
            virtual void operator()(ast_manager & m, expr_manager::store_expr_functor & to_save) {
                m_model = alloc(model, m);
            }
        };

        void get_model(model_ref & md) {
            // TODO
            mk_model mk(md);
            m_expr_manager.apply(mk);
        }

        proof * get_proof() {
            return 0;
        }

        std::string reason_unknown() const {
            return "unknown";
        }

        void set_cancel(bool f) {
            m_cancel = f;
            for (unsigned i = 0; i < num_plugins(); i++) {
                p(i).set_cancel(f);
            }
        }

        void display(std::ostream & out) const {
        }
    };
    
    kernel::kernel(ast_manager & m, bool proofs_enabled) {
        m_imp = alloc(imp, m, proofs_enabled);
    }

    kernel::~kernel() {
	SASSERT(m_imp);
	dealloc(m_imp);
    }

    void kernel::add_plugin(plugin * p) {
        m_imp->add_plugin(p);
    }
   
    void kernel::assert_expr(expr * f, proof * pr) {
        m_imp->assert_expr(f, pr);
    }
        
    void kernel::push() {
        m_imp->push(true);
    }
     
    void kernel::pop(unsigned num_scopes) {
        m_imp->pop(num_scopes, true);
    }

    lbool kernel::check_sat(unsigned num_assumptions, expr * const * assumptions) {
        return m_imp->check_sat(num_assumptions, assumptions);
    }
    
    void kernel::collect_statistics(statistics & st) const {
        m_imp->collect_statistics(st);
    }
    
    void kernel::get_unsat_core(ptr_vector<expr> & r) {
        m_imp->get_unsat_core(r);
    }

    void kernel::get_model(model_ref & m) {
        m_imp->get_model(m);
    }
    
    proof * kernel::get_proof() {
        return m_imp->get_proof();
    }
    
    std::string kernel::reason_unknown() const {
        return m_imp->reason_unknown();
    }

    void kernel::set_cancel(bool f) {
        m_imp->set_cancel(f);
    }
    
    void kernel::display(std::ostream & out) const {
        m_imp->display(out);
    }

};
