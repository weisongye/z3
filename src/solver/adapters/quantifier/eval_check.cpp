/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    eval_check.cpp

Abstract:

    <abstract>

Author:

    Andy Reynolds 2013-04-21.

--*/

#include"eval_check.h"
#include"ast_pp.h"
#include"model_construct.h"
#include"model_check.h"
#include"pattern_inference.h"

//#define EVAL_CHECK_DEBUG
#define USE_BINARY_SEARCH

using namespace qsolver;

struct lt_index {
public:
    static int compare(annot_entry * tc1, annot_entry * tc2) {
        SASSERT(tc1->get_size()==tc2->get_size());
        for (unsigned i=0; i<tc1->get_size(); i++) {
            if (tc1->get_value(i)<tc2->get_value(i)) {
                return 1;
            }
            else if (tc1->get_value(i)>tc2->get_value(i)) {
                return -1;
            }
        }
        return 0;
    }
    static int compare(expr_ref_buffer & vals, annot_entry * tc2) {
        SASSERT(vals.size()==tc2->get_size());
        for (unsigned i=0; i<vals.size(); i++) {
            if (vals[i]<tc2->get_value(i)) {
                return 1;
            }
            else if (vals[i]>tc2->get_value(i)) {
                return -1;
            }
        }
        return 0;
    }
public:
    simple_def & m_sdf;
    lt_index(simple_def & sdf) : m_sdf(sdf) {}
    bool operator()(annot_entry * tc1, annot_entry * tc2) const {
        return compare(tc1, tc2) == -1;
    }
};


annot_entry * annot_entry::mk(mc_context & mc, unsigned arity) {
    //small_object_allocator & allocator = _m.get_allocator();
    void * mem  = mc.allocate(sizeof(expr) + arity * 2 * sizeof(expr*) );
    return new (mem) annot_entry(arity);
}


bool annot_entry::is_value() {
    for (unsigned i=0; i<get_size(); i++) {
        if (!m_vec[i]) {
            return false;
        }
    }
    return true;
}

bool annot_entry_trie::add(mc_context & mc, annot_entry * c, unsigned index, unsigned data_val) {
    if (index==c->get_size()) {
        if (m_data==0) {
            m_data = data_val+1;
            return true;
        }
        else {
            return false;
        }
    }
    else {
        expr * curr = c->get_value(index);
        annot_entry_trie * ct;
        if (m_children.find(curr, ct)) {
            return ct->add(mc, c, index+1, data_val);
        }
        else {
            void * mem = mc.allocate(sizeof(annot_entry_trie));
            ct = new (mem) annot_entry_trie;
            m_children.insert(curr, ct);
            return ct->add(mc, c, index+1, data_val);
        }
    }
}

bool annot_entry_trie::evaluate(annot_entry * c, unsigned index, unsigned & data_val) {
    if (index==c->get_size()) {
        if (m_data==0) {
            return false;
        }
        else {
            data_val = m_data-1;
            return true;
        }
    }
    else {
        annot_entry_trie * ct;
        if (m_children.find(c->get_value(index), ct)) {
            return ct->evaluate(c, index+1, data_val);
        }
        else {
            return false;
        }
    }
}

bool annot_entry_trie::evaluate(expr_ref_buffer & vals, unsigned index, unsigned & data_val) {
    if (index==vals.size()) {
        if (m_data==0) {
            return false;
        }
        else {
            data_val = m_data-1;
            return true;
        }
    }
    else {
        annot_entry_trie * ct;
        if (m_children.find(vals[index], ct)) {
            return ct->evaluate(vals, index+1, data_val);
        }
        else {
            return false;
        }
    }
}

#ifdef USE_BINARY_SEARCH

void simple_def::sort_entries() {
    if (!m_sorted) {
        //sort the definition
        lt_index lti(*this);
        std::sort(m_conds.begin(), m_conds.end(), lti);
        //for (unsigned i=0; i<(m_conds.size()-1); i++) {
        //    SASSERT(lt_index::compare(m_conds[i],m_conds[i+1])==-1;);
        //}
        m_sorted = true;
    }
}

bool simple_def::get_index_of(annot_entry * c, unsigned & index) {
    unsigned sz = m_conds.size();
    if (sz == 0) {
        return false;
    }
    sort_entries();
    int low  = 0;
    int high = sz - 1;
    while (true) {
        int mid            = low + ((high - low)/2);
        int s = lt_index::compare(c, m_conds[mid]);
        if (s > 0) {
            low = mid + 1;
        }
        else if (s < 0) {
            high = mid - 1;
        }
        else {
            index = mid;
            return true;
        }
        if (low > high) {
            return false;
        }
    }
    SASSERT(false);
    return false;
}

expr * simple_def::evaluate(annot_entry * c, bool partial) {
    unsigned index;
    if (get_index_of(c, index)) {
        return m_conds[index]->get_result();
    }
    return partial ? 0 : m_else;
}

annot_entry * simple_def::get_entry(expr_ref_buffer & vals) {
    unsigned sz = m_conds.size();
    if (sz == 0) {
        return 0;
    }
    sort_entries();
    int low  = 0;
    int high = sz - 1;
    while (true) {
        int mid            = low + ((high - low)/2);
        int s = lt_index::compare(vals, m_conds[mid]);
        if (s > 0) {
            low = mid + 1;
        }
        else if (s < 0) {
            high = mid - 1;
        }
        else {
            return m_conds[mid];
        }
        if (low > high) {
            return 0;
        }
    }
    SASSERT(false);
    return 0;
}

expr * simple_def::evaluate(expr_ref_buffer & vals, bool partial) {
    annot_entry * ae = get_entry(vals);
    if (ae) {
        return ae->get_result();
    }
    return partial ? 0 : m_else;
}

bool simple_def::is_repair_entry(annot_entry * c) {
    SASSERT(m_unsorted_conds.contains(c));
    return m_unsorted_repair_conds.contains(c);
}

bool simple_def::append_entry(mc_context & mc, annot_entry * c, bool is_repair) {
    unsigned index;
    if (!get_index_of(c, index)) {
        m_sorted = false;
        m_conds.push_back(c);
        m_unsorted_conds.push_back(c);
        if (is_repair) {
            m_unsorted_repair_conds.push_back(c);
        }
        return true;
    }
    else {
        /*
        std::cout << "Compare \n";
        mc.display(std::cout, c);
        std::cout << "\n";
        mc.display(std::cout, m_conds[index]);
        std::cout << "\n";
        for (unsigned i=0; i<c->get_size(); i++) {
            //make the annotation small if need be
        }
        */
    }
    return false;
}


#else

expr * simple_def::evaluate(annot_entry * c, bool partial) {
    unsigned index;
    if (m_tct.evaluate(c, index)) {
        return m_conds[index]->get_result();
    }
    return partial ? 0 : m_else;
}

expr * simple_def::evaluate(expr_ref_buffer & vals, bool partial) {
    unsigned index;
    if (m_tct.evaluate(vals, index)) {
        return m_conds[index]->get_result();
    }
    return partial ? 0 : m_else;
}

bool simple_def::append_entry(mc_context & mc, annot_entry * c) {
    SASSERT(c->is_value());
    if (m_tct.add(mc, c, m_conds.size())) {
        m_conds.push_back(c);
        m_unsorted_conds.push_back(c);
        return true;
    }
    else {
        return false;
    }
}
#endif

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

void eval_node::notify_value(expr * ev) {
    m_value = ev;
    //if (m_m.is_true(ev) || m_m.is_false(ev)) {
        //check if parents can evaluate
        //for (unsigned i=0; i<m_parents.size(); i++) {
        //}
    //}
}

void eval_node::unnotify_evaluation() {
    for (unsigned i=0; i<m_parents.size(); i++) {
        m_parents[i]->m_children_eval_count--;
    }
}


bool eval_node::is_basic_trigger( expr * e, ptr_buffer<expr> & vars, ptr_buffer<expr> & terms ) {
    if (is_uninterp(e)) {
        for (unsigned i=0; i<to_app(e)->get_num_args(); i++) {
            expr * ec = to_app(e)->get_arg(i);
            if (is_var(ec)) {
                if (!vars.contains(ec)) {
                    vars.push_back(ec);
                }
            }
            else if (!is_ground(ec)) {
                if (!is_basic_trigger(ec, vars, terms)) {
                    return false;
                }
            }
        }
        terms.push_back(e);
        return true;
    }else {
        return false;
    }
}



eval_check::eval_check(ast_manager & _m) : m_m(_m) {
    m_inst_limited = true;
    m_multiple_patterns = true;
    m_ground_partial_evaluation = false;
    m_simple_pattern_match = true;
}

eval_check::~eval_check() {
  m_pattern_quants.reset();
  m_ematcher.reset();
}

void eval_check::reset_round() {
    m_eval_nodes.reset();
    m_filter_inst_cache = false;
  m_pattern_quants.reset();
  m_ematcher.reset();
}


void eval_check::set_var_bind_eval_node(eval_node * en, unsigned vid) {
    if (!m_bind_terms.contains(vid)) {
        ptr_vector< eval_node > vec;
        vec.push_back(en);
        m_bind_terms.insert(vid, vec);
        en->m_vars_to_bind++;
    }
    else {
        ptr_vector< eval_node > & vec = m_bind_terms.find(vid);
        if (!vec.contains(en)) {
            vec.push_back(en);
            en->m_vars_to_bind++;
        }
    }

}

void eval_check::set_var_bound(unsigned vid, ptr_vector<eval_node> & new_active) {
    if (m_vars[vid]) {
        m_vars[vid]->notify_evaluation(new_active);
    }

    if (m_bind_terms.contains(vid)) {
        ptr_vector< eval_node > & vec = m_bind_terms.find(vid);
        for (unsigned i=0; i<vec.size(); i++) {
            vec[i]->m_vars_to_bind--;
        }
    }

}

void eval_check::set_var_unbound(unsigned vid) {
    if (m_vars[vid]) {
        m_vars[vid]->unnotify_evaluation();
    }

    if (m_bind_terms.contains(vid)) {
        ptr_vector< eval_node > & vec = m_bind_terms.find(vid);
        for (unsigned i=0; i<vec.size(); i++) {
            vec[i]->m_vars_to_bind++;
        }
    }

}


void eval_check::set_counters(mc_context & mc, model_constructor * mct, func_decl * f) {
    if (!m_func_num_entries.contains(f)) {
        simple_def * df = mct->get_simple_def(mc,f);
        m_func_num_entries.insert(f, df->get_num_entries());
        m_func_num_real_entries.insert(f, df->get_num_entries()-df->get_num_repair_entries());
    }
}

eval_node * eval_check::mk_eval_node(mc_context & mc, model_constructor * mct, expr * e, ptr_vector<eval_node> & active, obj_map< expr, eval_node *> & evals, unsigned q_depth) {
    eval_node * ene;
    if (evals.find(e, ene)) {
        return ene;
    }
    else {
        if (!m_eval_nodes.find(e, ene)) {
            void * mem = mc.allocate(sizeof(eval_node));
            ene = new (mem) eval_node(e);
            m_eval_nodes.insert(e, ene);
        }
        ene->reset();
        ene->m_q_depth = q_depth;
        //first check if it is a basic trigger
        bool initializedNode = false;
        if (is_uninterp(e)) {
            ptr_buffer<expr> vars;
            ptr_buffer<expr> terms;
            /*
            if (eval_node::is_basic_trigger(e, vars, terms)) {
                for (unsigned i=0; i<vars.size(); i++) {
                    set_var_bind_eval_node(ene, to_var(vars[i])->get_idx());
                }
                //store number of entries for function
                for (unsigned i=0; i<terms.size(); i++) {
                    set_counters(mc, mct, to_app(terms[i])->get_decl());
                }
            }
            */
        }
        if (!initializedNode) {
            if (!is_ground(e) && is_app(e)) {
                for (unsigned i=0; i<to_app(e)->get_num_args(); i++) {
                    expr * ec = to_app(e)->get_arg(i);
                    if (mc.is_atomic_value(ec)) {
                        ene->m_children_eval_count++;
                        ene->m_children.push_back(0);
                    }
                    else if (is_uninterp(e) && is_var(ec)) {
                        ene->m_children_eval_count++;
                        ene->m_children.push_back(0);
                        set_var_bind_eval_node(ene, to_var(ec)->get_idx());
                    }
                    else {
                        eval_node * enec = mk_eval_node(mc, mct, ec, active, evals, q_depth+1);
                        enec->add_parent(ene);
                    }
                }
            }
            if (is_ground(e) || ene->can_evaluate()) {
                active.push_back(ene);
            }
            if (is_var(e)) {
                unsigned vid = to_var(e)->get_idx();
                m_vars[vid] = ene;
            }
            if (is_uninterp(e)) {
                //store number of entries for function
                func_decl * f = to_app(e)->get_decl();
                set_counters(mc, mct, f);
            }
        }
        evals.insert(e, ene);
        return ene;
    }
}

lbool eval_check::run(mc_context & mc, model_constructor * mct, quantifier * q, expr_ref_buffer & instantiations) {
    if( m_simple_pattern_match ){
      TRACE("eval_check", tout << "Run eval check on " << mk_pp(q,m_m) << "\n";);
      return do_pattern_match( mc, mct, q, instantiations );
    }
    else{

      m_var_bind_count = 0;
      m_vars.reset();
      m_vars.resize(q->get_num_decls(),0);
      m_bind_terms.reset();
      ptr_vector<eval_node> active;
      obj_map< expr, eval_node *> evals;
      m_func_num_entries.reset();
      m_func_num_real_entries.reset();
      mk_eval_node(mc, mct, q->get_expr(), active, evals);

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
      m_depth = 0;
      //std::cout << "Eval check " << mk_pp(q,m_m) << "..." << std::endl;

      unsigned prev_size = active.size();
      expr_ref_buffer vsub(m_m);
      expr_ref_buffer esub(m_m);
      for (unsigned i=0; i<q->get_num_decls(); i++) {
          vsub.push_back(0);
          esub.push_back(0);
      }
      m_start_index.reset();
      m_start_score = 0;
      do {
          m_first_time = true;
          m_process_repair_entries = true;//false;
          if (do_eval_check(mc, mct, q, active, vsub, esub, instantiations)==l_false) {
              TRACE("eval_check", tout << "Eval check failed\n";);
              return instantiations.empty() ? l_undef : l_false;
          }
          else {
              TRACE("eval_check", tout << "Eval check succeeded " << instantiations.size() << " " << m_start_index.size() << "\n";);
              for (unsigned i=0; i<esub.size(); i++) {
                  SASSERT(!esub[i]);
                  SASSERT(!vsub[i]);
              }
              SASSERT(active.size()==prev_size);
              /*
              if (instantiations.empty()) {
                  TRACE("eval_check", tout << "Eval check quantifier, now considering repair entries\n";);
                  //try on repair entries as well
                  m_first_time = true;
                  m_start_index.reset();
                  m_start_score = 0;
                  m_process_repair_entries = true;
                  if (do_eval_check(mc, mct, q, active, vsub, esub, instantiations)==l_false) {
                      return instantiations.empty() ? l_undef : l_false;
                  }
                  else {
                      SASSERT(active.size()==prev_size);
                  }
              }
              */
          }
          //std::cout << "Done." << std::endl;
      } while (m_multiple_patterns);   //&& instantiations.empty()

      return instantiations.empty() ? l_undef : l_false;
  }
}

lbool eval_check::do_eval_check(mc_context & mc, model_constructor * mct, quantifier * q, ptr_vector<eval_node> & active,
                                expr_ref_buffer & vsub, expr_ref_buffer & esub, expr_ref_buffer & instantiations) {
    m_depth++;
    lbool eresult = l_undef;
    unsigned prev_size = active.size();
    bool firstTime = m_first_time;
    if (!active.empty()) {
        unsigned best_index = active.size()-1;
        unsigned max_score = 0;
        unsigned max_score2 = 0;
        unsigned max_score3 = 0;
        for (unsigned i=0; i<active.size(); i++) {
            unsigned ii = (active.size()-1)-i;
            if (active[ii]->can_evaluate() && (!m_first_time || !m_start_index.contains(ii))) {
                unsigned score = 1 + active[ii]->m_vars_to_bind; //TODO : more heuristics
                if (score>=max_score) {
                    unsigned score2 = 1;// + (10000-active[ii]->m_q_depth);
                    if (score>max_score || score2>=max_score2) {
                        //expr * e = active[ii]->get_expr();
                        unsigned score3 = 1;
                        if (score>max_score || score2>max_score2 || score3>max_score3) {
                            best_index = ii;
                            max_score = score;
                            max_score2 = score2;
                            max_score3 = score3;
                        }
                    }
                }
            }
        }
        if (!active[best_index]->can_evaluate()) {
            return l_false;
        }
        eval_node * en = active[best_index];
        active.erase(active.begin()+best_index);
        expr * e = en->get_expr();
        if (m_first_time) {
            if (m_start_index.contains(best_index) || max_score<m_start_score) {
                return l_false;
            }
            else {
                m_start_index.push_back(best_index);
            }
            TRACE("eval_check_select", tout << "Select " << mk_pp(e,m_m) << " as the best starting pattern.\n";
                                       if (is_uninterp(en->get_expr())) {
                                            simple_def * df = mct->get_simple_def(mc,to_app(e)->get_decl());
                                            //tout << "It has " << df->get_num_entries() << " entries.\n";
                                            tout << "It's definition is : \n";
                                            mc.display(tout, df);
                                            tout << "\n";
                                       });
            m_first_time = false;
            m_start_score = max_score;
        }


        /*
        std::cout << "Process " << mk_pp(e,m_m) << " at depth " << m_depth << ", qdepth is " << en->m_q_depth << ", vars to bind " << en->m_vars_to_bind << "\n";
        if (is_uninterp(e)) {
            std::cout << "Number of entries will be " << mct->get_simple_def(mc,to_app(e)->get_decl())->get_num_entries() << " " << mct->get_simple_def(mc,to_app(e)->get_decl())->get_num_repair_entries() << "\n";
        }
        */
        TRACE("eval_check_debug", tout << "Process " << mk_pp(e,m_m) << " at depth " << m_depth << ", qdepth is " << en->m_q_depth << "\n";
                                    tout << "Current entry is : \n";
                                    for (unsigned l=0; l<vsub.size(); l++) {
                                        if (vsub[l]) { mc.display(tout,vsub[l]); }else{tout << "*";}
                                        tout << " ";
                                    };
                                    tout << "\n";);
        expr * result = 0;
        if (is_ground(e)) {
            //just use the evaluator
            result = mc.evaluate(mct, e, m_ground_partial_evaluation);
        }
        else {
            SASSERT(is_app(e));
            //evaluate the expression
            expr_ref_buffer children(m_m);
            sbuffer<unsigned> var_to_bind;
            for (unsigned i=0; i<to_app(e)->get_num_args(); i++) {
                if (en->get_child(i)) {
                    children.push_back(en->get_child(i)->get_evaluation());
                }
                else {
                    expr * ec = to_app(e)->get_arg(i);
                    if (mc.is_atomic_value(ec)) {
                        children.push_back(ec);
                    }
                    else {
                        if (is_uninterp(e) && is_var(ec)) {
                            var * v = to_var(ec);
                            //check if v is already bound
                            unsigned vid = v->get_idx();
                            expr * val_made = 0;
                            if (vsub[vid]) {
                                val_made = vsub[vid];
                            }
                            else {
                                if (!var_to_bind.contains(vid)) {
                                    var_to_bind.push_back(vid);

                                }
                                val_made = v;
                            }
                            children.push_back(val_made);
                        }
                        else {
                            //don't know how to evaluate (start trying relevant domain?)
                            SASSERT(false);
                            return l_false;
                        }
                    }
                }
            }
            if (var_to_bind.size()!=en->m_vars_to_bind) {
                TRACE("eval_check_warn", tout << "WARNING: " << mk_pp(en->get_expr(),m_m) << " has to bind " << en->m_vars_to_bind << ", different than " << var_to_bind.size() << "\n";);
            }
            SASSERT(var_to_bind.size()==en->m_vars_to_bind);
            func_decl * f = to_app(e)->get_decl();
            //compute the definition
            if (is_uninterp(f)) {
                simple_def * df = mct->get_simple_def(mc,f);
                if (!var_to_bind.empty()) {
                    m_var_bind_count += var_to_bind.size();
                    ptr_vector<eval_node> new_active;
                    if (m_var_bind_count<q->get_num_decls()) {
                        //have each newly bound variable notify that they evaluate
                        for (unsigned j=0; j<var_to_bind.size(); j++) {
                            SASSERT(vsub[var_to_bind[j]]==0);
                            set_var_bound(var_to_bind[j], new_active);
                        }
                        //as well as this node
                        en->notify_evaluation(new_active);
                        if (!new_active.empty()) {
                            TRACE("eval_check_debug", for (unsigned i=0; i<new_active.size(); i++) {
                                                          tout << "Now active : " << mk_pp(new_active[i]->get_expr(),m_m) << "\n";
                                                      } );
                            new_active.append(active.size(), active.c_ptr());
                        }
                    }
                    SASSERT(df->get_else());
                    TRACE("eval_check_debug", tout << "Process definition : ";
                                              mc.display(tout, df);
                                              tout << "\n";
                                              tout << "With arguments : \n";
                                                for (unsigned l=0; l<children.size(); l++) {
                                                    tout << "   ";
                                                    mc.display(tout, children[l]);
                                                    tout << "\n";
                                                };
                                                );
                    //unsigned process_num_entries = df->get_num_entries();// - df->get_num_repair_entries();
                    unsigned process_num_entries = m_process_repair_entries ? m_func_num_entries.find(f) : m_func_num_real_entries.find(f);
                    for (unsigned i=0; i<process_num_entries; i++) {
                    //for (unsigned i=0; i<df->get_num_entries(); i++) {
                        annot_entry * cf = df->get_condition(i);
                        if (mc.do_compose(vsub, children, esub, cf)) {
                            for (unsigned j=0; j<var_to_bind.size(); j++) {
                                if (m_vars[var_to_bind[j]]) {
                                    m_vars[var_to_bind[j]]->notify_value(vsub[var_to_bind[j]]);
                                }
#ifdef EVAL_CHECK_DEBUG
                                expr * ve = mc.evaluate(mct, esub[(vsub.size()-1)-var_to_bind[j]]);
                                if (ve!=vsub[var_to_bind[j]]) {
                                    TRACE("eval_check_warn", tout << "Bad term : " << mk_pp(esub[(vsub.size()-1)-var_to_bind[j]], m_m) << "\n";
                                                             tout << "Evaluates to "; mc.display(tout,ve); tout << ", not equal to "; mc.display(tout, vsub[var_to_bind[j]]); tout << "\n";);
                                    SASSERT(false);
                                }
#endif
                            }
                            TRACE("eval_check_debug", tout << "Process entry : ";
                                                        for (unsigned l=0; l<vsub.size(); l++) {
                                                            if (vsub[l]) { mc.display(tout,vsub[l]); }else{tout << "*";}
                                                            tout << " ";
                                                        }
                                                        );
                            //TRACE("eval_check_debug", tout << "Process entry "; mc.display(tout, dc->get_condition(i)); tout << "\n";);
                            if (m_var_bind_count<q->get_num_decls()) {
                                en->notify_value(df->get_value(i));
                                if (new_active.empty()) {
                                    if (en->get_expr()!=q->get_expr() || m_m.is_false(en->m_value)) {
                                        //SASSERT(!active.empty() || en->get_expr()==q->get_expr());
                                        eresult = do_eval_check(mc, mct, q, active, vsub, esub, instantiations);
                                        if (eresult==l_false) {
                                            return l_false;
                                        }
                                    }
                                }
                                else {
                                    eresult = do_eval_check(mc, mct, q, new_active, vsub, esub, instantiations);
                                    if (eresult==l_false) {
                                        return l_false;
                                    }
                                }
                            }
                            else {
                                TRACE("eval_check_debug", tout << "Add instantiation now.\n";);
                                //just do the evaluation now
                                //we have an instantiation
                                for (unsigned k=0; k<vsub.size(); k++) {
                                    SASSERT(vsub[k]);
                                    SASSERT(esub[k]);
                                }
                                if (mc.add_instantiation(mct, q, esub, vsub, instantiations, m_filter_inst_cache, true, false)) {
                                    eresult = l_true;
                                }
                                TRACE("eval_check_debug", tout << "Finished instantiation.\n";);
                            }
                        }

                        //undo the match
                        for (unsigned j=0; j<var_to_bind.size(); j++) {
                            vsub.set(var_to_bind[j], 0);
                            esub.set((vsub.size()-1)-var_to_bind[j], 0);
                        }
                        if (!firstTime && eresult==l_true && m_inst_limited) {
                            SASSERT(!instantiations.empty());
                            break;
                        }
                    }
                    if (m_var_bind_count<q->get_num_decls()) {
                        en->unnotify_evaluation();
                        for (unsigned j=0; j<var_to_bind.size(); j++) {
                            set_var_unbound(var_to_bind[j]);
                        }
                    }
                    m_var_bind_count -= var_to_bind.size();

                    // if no instantiations, now try default
                    //if (!firstTime && instantiations.empty()) {
                     //   result = df->get_else();
                    //}
                }
                else {
                    //just evaluate
                    result = df->evaluate(children, m_ground_partial_evaluation);
                }
            }
            else {
                TRACE("eval_term_debug", tout << "evaluate for " << mk_pp(e, m_m) << "\n";);
                //just evaluate
                result = mc.evaluate_interp(f, children);
            }
        }
        // if processing a simple result, just recurse
        if (result) {
            TRACE("eval_check_debug", tout << "Evaled, lookup got "; mc.display(tout, result); tout << "\n";);
            ptr_vector<eval_node> new_active;
            en->notify_evaluation(new_active);
            en->notify_value(result);
            if (new_active.empty()) {
                if (en->get_expr()!=q->get_expr() || m_m.is_false(en->m_value)) {
                    if (active.empty() && en->get_expr()!=q->get_expr()) {
                        SASSERT(m_var_bind_count<q->get_num_decls());
                        TRACE("eval_check_warn", tout << "WARNING: Evaluation finished and not all variables are bound.\n";);
                        return l_false;
                    }
                    else {
                        eresult = do_eval_check(mc, mct, q, active, vsub, esub, instantiations);
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
                eresult = do_eval_check(mc, mct, q, new_active, vsub, esub, instantiations);
            }
            en->m_value = 0;
            en->unnotify_evaluation();
        }
        //put it back into active
        active.push_back(en);
    }
    else {
        SASSERT(m_var_bind_count<q->get_num_decls());
        TRACE("eval_check_warn", tout << "Did not bind all variables in quantifier " << mk_pp(q,m_m) << "\n";
                                 tout << "WARNING: no terms to evaluate.\n";);
        return l_false;
    }
    m_depth--;
    SASSERT(eresult==l_false || active.size()==prev_size);
    return eresult;
}






lbool eval_check::do_pattern_match(mc_context & mc, model_constructor * mct, quantifier * q, expr_ref_buffer & instantiations) {
  quantifier * qp;
  if (!m_pattern_quants.find(q, qp)) {
    pattern_inference_params p;
    pattern_inference pi(m_m, p);
    expr_ref  new_n(m_m);
    proof_ref new_pr(m_m);
    pi(q, new_n, new_pr);
    TRACE("eval_check_pi", tout << "Expr : " << mk_pp(q,m_m) << "\n";tout << "Patterned : " << mk_pp( new_n, m_m) << "\n";);
    qp = to_quantifier(new_n);
    TRACE("eval_check_pi", tout << "# patterns = " << qp->get_num_patterns() <<"\n";
                    for(unsigned i=0; i<qp->get_num_patterns(); i++){
                      tout << mk_pp(qp->get_pattern(i),m_m) << "\n";
                    });
    m_pattern_quants.insert( q, qp );
    ptr_vector< ematcher > em_pats;
    //create sequential matching object
    for(unsigned i=0; i<qp->get_num_patterns(); i++){
      ematcher * curr = 0;
      ematcher * init = 0;
      //for(unsigned k=0; k<qp->get_num_patterns(); k++){
        for (unsigned j=0; j<to_app(qp->get_pattern(i))->get_num_args(); j++) {
          unsigned use_j = j;//(j+k)%to_app(qp->get_pattern(i))->get_num_args();
          //make the matcher
          ptr_vector< ematcher > ems;
          void * mem  = mc.allocate(sizeof(ematcher) );
          ematcher * em = new (mem) ematcher( m_m,to_app(qp->get_pattern(i))->get_arg(use_j) );
          ems.push_back( em );
          if (!init) {
            init = em;
          }
          TRACE("eval_check_pi_debug", tout << "Process pattern " << mk_pp(qp->get_pattern(i),m_m) << "\n";);
          while (!ems.empty()) {
            ematcher * emp = ems[ems.size()-1];
            ems.pop_back();
            if (curr) {
              curr->m_next = emp;
            }
            curr = emp;
            //process emp
            for (unsigned i=0; i<to_app(emp->m_curr)->get_num_args(); i++) {
              expr * ec = to_app(emp->m_curr)->get_arg(i);
              if (!is_ground(ec) && !is_var(ec)) {
                TRACE("eval_check_pi_debug", tout << "Process pattern arg " << mk_pp(ec,m_m) << "\n";);
                void * mem  = mc.allocate(sizeof(ematcher) );
                ematcher * empc = new (mem) ematcher(m_m, ec);
                ems.push_back( empc );
                curr->m_children.insert( i, empc );
              }
            }
          }
        }
        TRACE("eval_check_pi", tout << "Will process in this order : \n";
                               ematcher * tmp = init;
                               while (tmp) {
                                  tout << mk_pp(tmp->m_curr,m_m) << "\n";
                                  tmp = tmp->m_next;
                               }
                               tout << "\n";);
        em_pats.push_back( init );
      }
    //}
    m_ematcher.insert( q, em_pats );
  }
  lbool eresult = l_undef;
  ptr_vector<ematcher> & evec = m_ematcher.find(q);
  for (unsigned i=0; i<evec.size(); i++) {
    expr_ref_buffer vsub(m_m);
    expr_ref_buffer esub(m_m);
    for (unsigned j=0; j<q->get_num_decls(); j++) {
        vsub.push_back(0);
        esub.push_back(0);
    }
    evec[i]->reset(m_m, mc, mct);
    if (do_ematching(mc, mct, q, evec[i], vsub, esub, instantiations )==l_false) {
      eresult = l_false;
    }
  }
  return eresult;
}

lbool eval_check::do_ematching(mc_context & mc, model_constructor * mct, quantifier * q, ematcher * curr,
                               expr_ref_buffer & vsub, expr_ref_buffer & esub, expr_ref_buffer & instantiations) {
  if (!curr) {
    TRACE("ec_inst", tout << "Possible instantiation for " << mk_pp(q,m_m) << ": \n";
                      for (unsigned i=0; i<vsub.size(); i++) {
                        if (vsub[i] && esub[i]) {
                          tout << "   " << mk_pp(vsub[i],m_m) << " : " << mk_pp(esub[(q->get_num_decls()-1)-i],m_m) << "\n";
                        }
                      });
    //add instantiation
    if (mc.add_instantiation(mct, q, esub, vsub, instantiations, false, true, false)) {
      return l_false;
    }else{
      return l_undef;
    }
  }else{
    lbool eresult = l_undef;
    expr * e = curr->m_curr;
    SASSERT( is_app(e) );
    func_decl * f = to_app(e)->get_decl();
    SASSERT(is_uninterp(f));
    simple_def * df = mct->get_simple_def(mc,f);
    unsigned process_num_entries = df->get_num_entries();
    for (unsigned i=0; i<process_num_entries; i++) {
      annot_entry * cf = df->get_condition(i);
      TRACE("ec_inst_debug", tout << "match " << mk_pp(e,m_m) << " against "; mc.display(tout,cf); tout << "\n";
                             tout << "current match : ";
                             for (unsigned j=0; j<esub.size(); j++) {
                               unsigned ju = (q->get_num_decls()-1)-j;
                               if (esub[ju]){ tout << mk_pp(esub[ju],m_m); }else{ tout << "*"; }
                               tout << " ";
                             }
                             tout << "\n";);
      if (curr->m_eqc==0 || curr->m_eqc==cf->get_result()) {
        bool success = true;
        u_map< expr * > vprev;
        u_map< expr * > eprev;
        expr_ref_buffer tmp(m_m);
        for (unsigned j=0; j<to_app(e)->get_num_args(); j++) {
          expr * ec = to_app(e)->get_arg(j);
          expr * cc = cf->get_value(j);
          TRACE("ec_inst_debug", tout << "Process argument " << mk_pp(ec,m_m) << "\n";);
          if (is_ground(ec)) {
            SASSERT(curr->m_ground_eval.contains(j));
            if (curr->m_ground_eval.find(j)!=cc) {
              success = false;
              break;
            }
          }else if (is_var(ec)) {
            unsigned vid = to_var(ec)->get_idx();
            //TRACE("ec_inst_debug", tout << "Process variable " << vid << " " << vsub.size() << " " << esub.size() << " " << (vsub[vid]!=cc) << " " << (vsub[vid]!=0) << "\n";);
            if (vsub[vid]!=cc) {
              if (vsub[vid]!=0) {
                success = false;
                break;
              }else{
                if (!vprev.contains(vid)) {
                  tmp.push_back(vsub[vid]);
                  tmp.push_back(esub[vid]);
                  vprev.insert(vid, vsub[vid]);
                  eprev.insert(vid, esub[(q->get_num_decls()-1)-vid]);
                }
                vsub.set(vid, cc);
                esub.set((q->get_num_decls()-1)-vid, cf->get_annotation(j));
              }
            }
            //TRACE("ec_inst_debug", tout << "Done with variable " << vid << "\n";);
          }else{
            SASSERT(curr->m_children.contains(j));
            curr->m_children.find(j)->m_eqc = cc;
          }
        }
        if (success) {
          //TRACE("ec_inst_debug", tout << "recurse...\n";);
          if (do_ematching( mc, mct, q, curr->m_next, vsub, esub, instantiations )==l_false) {
            eresult = l_false;
          }
        }
        //TRACE("ec_inst_debug", tout << "undo changes...\n";);
        //undo changes
        for (unsigned j=0; j<q->get_num_decls(); j++) {
          if (vprev.contains(j)) {
            vsub.set( j, vprev[j]);
            esub.set( (q->get_num_decls()-1)-j, eprev[j]);
          }
        }
        //TRACE("ec_inst_debug", tout << "done.\n";);
      }
    }
    return eresult;
  }
}

void ematcher::reset(ast_manager & _m, mc_context & mc, model_constructor * mct) {
  m_eqc = 0;
  m_ground_eval.reset();
  for (unsigned i=0; i<to_app(m_curr)->get_num_args(); i++) {
    expr * ec = to_app(m_curr)->get_arg(i);
    if (is_ground(ec)) {
      expr_ref ee(_m);
      ee = mc.evaluate(mct, ec);
      m_ground_eval.insert(i, ee);
    }
  }
  if (m_next) {
    m_next->reset( _m, mc, mct );
  }
}