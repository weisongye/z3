/*++
  Copyright (c) 2013 Microsoft Corporation

  Module Name:

  predabst_context.cpp

  Abstract:

  Bounded PREDABST (symbolic simulation using Z3) context.

  Author:

  Nikolaj Bjorner (nbjorner) 2013-04-26
  Modified by Andrey Rybalchenko (rybal) 2014-3-7.

  Revision History:

  --*/

#include "predabst_context.h"
#include "dl_context.h"
#include "unifier.h"
#include "var_subst.h"
#include "substitution.h"
#include "smt_kernel.h"
#include "dl_transforms.h"

namespace datalog {

  class predabst::imp {
    struct stats {
      stats() { reset(); }
      void reset() { memset(this, 0, sizeof(*this)); }
      unsigned m_num_unfold;
      unsigned m_num_no_unfold;
      unsigned m_num_subsumed;
    };

    context&               m_ctx;         // main context where (fixedpoint) constraints are stored.
    ast_manager&           m;             // manager for ASTs. It is used for managing expressions
    rule_manager&          rm;            // context with utilities for fixedpoint rules.
    smt_params             m_fparams;     // parameters specific to smt solving
    smt::kernel            m_solver;      // basic SMT solver class
    var_subst              m_var_subst;   // substitution object. It gets updated and reset.
    volatile bool          m_cancel;      // Boolean flag to track external cancelation.
    stats                  m_stats;       // statistics information specific to the CLP module.

    typedef obj_map<func_decl, std::pair<expr * const *, expr_ref_vector *> > 
    func_decl2vars_preds;
    func_decl2vars_preds m_func_decl2vars_preds;

    typedef u_map<expr *> id2expr;
    id2expr m_rule2gbody;

    typedef u_map<vector<expr_ref_vector> > id2preds_vector;
    id2preds_vector m_rule2gpreds_vector; 

    typedef obj_map<func_decl, uint_set> func_decl2uints;
    func_decl2uints m_func_decl_body2rules;

    expr_ref_vector m_empty_preds;

    ast_ref_vector m_ast_trail;

    unsigned m_node_counter;
    typedef vector<bool> cube_t;

    typedef u_map<func_decl *> node2func_decl;
    node2func_decl m_node2func_decl;

    typedef u_map<cube_t *> node2cube;
    node2cube m_node2cube;

    typedef vector<unsigned> node_vector;
    typedef uint_set node_set;

    typedef u_map<unsigned> node2rule;
    node2rule m_node2parent_rule;

    typedef u_map<node_vector> node2nodes;
    node2nodes m_node2parent_nodes;

    typedef obj_map<func_decl, node_set> func_decl2node_set;
    func_decl2node_set m_func_decl2max_reach_node_set;

    node_set m_node_worklist;

  public:
    imp(context& ctx):
      m_ctx(ctx), 
      m(ctx.get_manager()),
      rm(ctx.get_rule_manager()),
      m_solver(m, m_fparams),  
      m_var_subst(m, false),
      m_cancel(false),
      m_empty_preds(m),
      m_ast_trail(m),
      m_node_counter(0)
    {
      // m_fparams.m_relevancy_lvl = 0;
      m_fparams.m_mbqi = false;
      m_fparams.m_soft_timeout = 1000;
    }

    ~imp() {
      for (func_decl2vars_preds::iterator it = m_func_decl2vars_preds.begin(), 
	     end = m_func_decl2vars_preds.end(); it != end; ++it) 
	dealloc(it->m_value.second);
      for (node2cube::iterator it = m_node2cube.begin(), 
	     end = m_node2cube.end(); it != end; ++it)
	dealloc(it->m_value);
    }        

    lbool query(expr* query) {
      m_ctx.ensure_opened();
      rule_set& rules = m_ctx.get_rules();
      rm.mk_query(query, rules);
      // collect predicates and delete corresponding rules
      for (rule_set::iterator rules_it = rules.begin(), rules_end = rules.end();
	   rules_it != rules_end; ++rules_it) {
	rule* r = *rules_it;
	func_decl* head_decl = r->get_decl();
	std::string sym(head_decl->get_name().bare_str());
	if (r->get_uninterpreted_tail_size() != 0 
	    || sym.substr(0, 8) != "__pred__") continue;
	char* suffix = new char[sym.size()-8+1];
#pragma warning(push)
#pragma warning(disable:4996)
	strcpy(suffix, sym.substr(8).c_str());
#pragma warning(pop)
	func_decl* suffix_decl = 
	  m.mk_func_decl(symbol(suffix), head_decl->get_arity(), 
			 head_decl->get_domain(), head_decl->get_range());
	m_ast_trail.push_back(suffix_decl);
	// add predicates to m_func_decl2vars_preds
	expr_ref_vector* preds = alloc(expr_ref_vector, m);
	preds->reserve(r->get_tail_size());
	for (unsigned i = 0; i < r->get_tail_size(); ++i)
	  (*preds)[i] = r->get_tail(i);
	m_func_decl2vars_preds.
	  insert(suffix_decl, std::make_pair(r->get_head()->get_args(), preds));
	// rule is not used for inference
	rules.del_rule(r);
      }
      // for each rule: ground body and instantiate predicates for applications
      for (unsigned r_id = 0; r_id<rules.get_num_rules(); ++r_id) {
	rule* r = rules.get_rule(r_id);
	// prepare grounding substitution
	ptr_vector<sort> free_sorts;
	r->get_vars(m, free_sorts);
	expr_ref_vector rule_subst(m);
	rule_subst.reserve(free_sorts.size());
	for (unsigned i = 0; i < rule_subst.size(); ++i) 
	  rule_subst[i] = m.mk_fresh_const("c", free_sorts[i]);
	// conjoin constraints in rule body 
	expr_ref_vector conjs(m);
	conjs.reserve(r->get_tail_size()-r->get_uninterpreted_tail_size());
	for (unsigned i = r->get_uninterpreted_tail_size(); 
	     i < r->get_tail_size(); ++i)
	  conjs[i-r->get_uninterpreted_tail_size()] = r->get_tail(i);
	expr_ref conj(m.mk_and(conjs.size(), conjs.c_ptr()), m);
	// apply substitution
	m_var_subst(conj, rule_subst.size(), rule_subst.c_ptr(), conj);
	m_ast_trail.push_back(conj);
	// store ground body
	m_rule2gbody.insert(r_id, conj);
	// store instantiated predicates
	vector<expr_ref_vector> gpreds_vector;
	// store instantiation for body applications
	for (unsigned i = 0; i < r->get_uninterpreted_tail_size(); ++i) 
	  gpreds_vector.push_back(app_inst_preds(r->get_tail(i), rule_subst));
	// store instantiation for non-query head
	if (!rules.is_output_predicate(r->get_decl())) {
	  expr_ref_vector& hpreds = app_inst_preds(r->get_head(), rule_subst);
	  expr_ref_vector npreds(m);
	  npreds.reserve(hpreds.size());
	  for (unsigned i=0; i<hpreds.size(); ++i) 
	    npreds[i] = m.mk_not(hpreds[i].get());
	  gpreds_vector.push_back(npreds);
	}
	m_rule2gpreds_vector.insert(r_id, gpreds_vector);
	// map body func_decls to rule
	for (unsigned i = 0; i < r->get_uninterpreted_tail_size(); ++i)
	  m_func_decl_body2rules.
	    insert_if_not_there2(r->get_decl(i), uint_set())->get_data().
	    m_value.insert(r_id);
      }
      // initial abstract inference
      for (unsigned r_id = 0; r_id < rules.get_num_rules(); ++r_id) {
	rule* r = rules.get_rule(r_id);
	if (r->get_uninterpreted_tail_size() != 0) continue;
	optional<unsigned>& added_id =
	  add_node(r->get_decl(), cart_pred_abst_rule(r_id), r_id);
	if (added_id) check_node_property(rules, *added_id);
      }
      // process worklist
      while(!m_node_worklist.empty()) {
	/*
	print_inference_state();
	char name[256];
	std::cin.getline(name, 256);
	*/
	if (m_cancel) throw default_exception("predabst canceled");
	unsigned current_id = *m_node_worklist.begin();
	m_node_worklist.remove(current_id);
	inference_step(rules, current_id);
      }
      //      print_inference_state();
      return l_false;
    }

    void cancel() {
      m_cancel = true;
      m_solver.cancel();
    }
        
    void cleanup() {
      m_cancel = false;
      // TBD hmm?
      m_solver.reset_cancel();
    }

    void reset_statistics() {
      m_stats.reset();
    }

    void collect_statistics(statistics& st) const {
      // TBD hmm?
    }

    void display_certificate(std::ostream& out) const {
      // TBD hmm?
      std::cout << "inside display_certificate" << std::endl;
      expr_ref ans = get_answer();
      out << mk_pp(ans, m) << "\n";    
    }

    expr_ref get_answer() const {
      // TBD hmm?
      return expr_ref(m.mk_true(), m);
    }

    model_ref get_model() const {
      model_ref md = alloc(model, m);
      // reachable predicates are concretized
      for (func_decl2node_set::iterator 
	     it_decl = m_func_decl2max_reach_node_set.begin(),
	     end_decl = m_func_decl2max_reach_node_set.end();
	   it_decl != end_decl; ++it_decl) {
	if (it_decl->m_key->get_arity() == 0)
	  throw("predabst::get_model zero arity");
	func_decl2vars_preds::obj_map_entry* e = 
	  m_func_decl2vars_preds.find_core(it_decl->m_key);
	optional<expr*> disj;
	if (e) {
	  expr_ref_vector& preds = *e->get_data().get_value().second;
	  for (node_set::iterator it_node = it_decl->m_value.begin(),
		 end_node = it_decl->m_value.end(); it_node != end_node;
	       ++it_node) {
	    cube_t& cube = *m_node2cube[*it_node];
	    optional<expr*> conj;
	    for (unsigned i = 0; i < cube.size(); ++i) 
	      if (cube[i]) 
		conj = conj ? to_expr(m.mk_and(preds[i].get(), *conj))
		  : preds[i].get();
	    disj = disj ? to_expr(m.mk_or(*conj, *disj)) : *conj;
	  }
	} else {
	  disj = to_expr(m.mk_true());
	}
	func_interp* fi = alloc(func_interp, m, it_decl->m_key->get_arity());
	fi->set_else(expr_ref(*disj, m));
	md->register_decl(it_decl->m_key, fi);
      }
      func_decl_set false_func_decls;
      // unreachable body predicates are false
      for (func_decl2uints::iterator it = m_func_decl_body2rules.begin(),
	     end = m_func_decl_body2rules.end(); it != end; ++it) {
	if (it->m_key->get_arity() == 0)
	  throw("predabst::get_model zero arity");
	if (!m_func_decl2max_reach_node_set.contains(it->m_key)) 
	  false_func_decls.insert(it->m_key);
      }
      // unreachable head predicates are false
      rule_set& rules = m_ctx.get_rules();
      for (rule_set::iterator it = rules.begin(), end = rules.end(); it != end; ++it) {
	func_decl* head_decl = (*it)->get_decl();
	if (rules.is_output_predicate(head_decl)) continue;
	if (head_decl->get_arity() == 0)
	  throw("predabst::get_model zero arity");
	if (!m_func_decl2max_reach_node_set.contains(head_decl)) 
	  false_func_decls.insert(head_decl);
      }
      for (func_decl_set::iterator it = false_func_decls.begin(),
	     end = false_func_decls.end(); it != end; ++it) {
	func_interp* fi = alloc(func_interp, m, (*it)->get_arity());
	fi->set_else(expr_ref(m.mk_false(), m));
	md->register_decl(*it, fi);
      }
      return md;
    }

  private:
    // ground arguments of app using subst, and then instantiate each predicate
    // by replacing its free variables with grounded arguments of app
    expr_ref_vector app_inst_preds(app* appl, const expr_ref_vector& subst) {
      func_decl2vars_preds::obj_map_entry* e = 
	m_func_decl2vars_preds.find_core(appl->get_decl());
      if (!e) return m_empty_preds;
      expr* const * vars = e->get_data().get_value().first;
      // TODO const needed?
      expr_ref_vector& preds = *e->get_data().get_value().second;
      // ground appl arguments
      expr_ref subst_tmp(m);
      m_var_subst(appl, subst.size(), subst.c_ptr(), subst_tmp);
      // instantiation maps preds variables to head arguments
      expr_ref_vector inst(m);
      inst.reserve(appl->get_num_args());
      app* gappl = to_app(subst_tmp);
      for (unsigned i = 0; i < appl->get_num_args(); ++i) {
	unsigned idx = to_var(vars[i])->get_idx();
	if (idx>=inst.size())
	  inst.resize(idx+1);
	inst[idx] = gappl->get_arg(i);
      } 
      // preds instantiates to inst_preds
      expr_ref_vector inst_preds(m);
      inst_preds.reserve(preds.size());
      for (unsigned i = 0; i < preds.size(); ++i) {	      
	m_var_subst(preds[i].get(), inst.size(), inst.c_ptr(), subst_tmp);
	inst_preds[i] = subst_tmp;
      }
      return inst_preds;
    }

    cube_t* cart_pred_abst_rule(unsigned r_id, 
				const node_vector& nodes = node_vector()) {
      // get instantiated predicates
      vector<expr_ref_vector>& preds_vector = m_rule2gpreds_vector[r_id];
      m_solver.push();
      m_solver.assert_expr(m_rule2gbody[r_id]);
      // load abstract states for nodes
      for (unsigned pos = 0; pos < nodes.size(); ++pos) {
	cube_t& pos_cube = *m_node2cube[nodes[pos]];
	for (unsigned i = 0; i < preds_vector[pos].size(); ++i) 
	  if (pos_cube[i]) m_solver.assert_expr(preds_vector[pos][i].get());
      }
      if (m_solver.check() == l_false) {
	// unsat body
	m_solver.pop(1);
	return 0; // null pointer denotes unsat cube
      }
      // collect abstract cube
      cube_t* cube = alloc(cube_t);
      expr_ref_vector& head_preds = preds_vector.back();
      if (head_preds.empty()) return cube;
      cube->resize(head_preds.size());
      for (unsigned i = 0; i < head_preds.size(); ++i) {
	m_solver.push();
	m_solver.assert_expr(head_preds[i].get());
	(*cube)[i] = (m_solver.check() == l_false);
	m_solver.pop(1);
      }
      m_solver.pop(1);
      return cube;
    }

    optional<unsigned>
    add_node(func_decl* sym, cube_t* cube, 
	     unsigned r_id, const node_vector& nodes = node_vector()) {
      optional<unsigned> added_id;
      if (!cube) return added_id;
      func_decl2node_set::obj_map_entry * sym_nodes_entry =
	m_func_decl2max_reach_node_set.find_core(sym);
      if (sym_nodes_entry) { 
	// nodes exist at this sym
	node_set& sym_nodes = sym_nodes_entry->get_data().m_value;
	node_vector old_lt_nodes;
	for (node_set::iterator it = sym_nodes.begin(), end = sym_nodes.end();
	     it != end; ++it) {
	  cube_t& old_cube = *m_node2cube[*it];
	  // if cube implies existing cube then nothing to add
	  if (cube_leq(*cube, old_cube)) {
	    dealloc(cube);
	    return added_id;
	  }
	  // stronger old cubes will not be considered maximal
	  if (cube_leq(old_cube, *cube)) old_lt_nodes.push_back(*it);
	}
	// remove subsumed maximal nodes
	for (node_vector::iterator it = old_lt_nodes.begin(), 
	       end = old_lt_nodes.end(); it != end; ++it) {
	  sym_nodes.remove(*it);
	  m_node_worklist.remove(*it); // removing non-existent element is ok
	}
	sym_nodes.insert(m_node_counter);
      } else {
	m_func_decl2max_reach_node_set.insert_if_not_there2(sym, node_set())->
	  get_data().m_value.insert(m_node_counter);
      }
      m_node2func_decl.insert(m_node_counter, sym);
      m_node2cube.insert(m_node_counter, cube);
      m_node2parent_rule.insert(m_node_counter, r_id);
      m_node2parent_nodes.insert(m_node_counter, nodes);
      m_node_worklist.insert(m_node_counter);
      added_id = m_node_counter;
      m_node_counter++;
      return added_id;
    }

    void check_node_property(const rule_set& rules, unsigned id) {
      // TODO add proof construction
      if (rules.is_output_predicate(m_node2func_decl[id])) {
	std::cout << "property violation " << id;
	exit(1);
      }
    }

    // return whether c1 implies c2
    bool cube_leq(const cube_t& c1, const cube_t& c2) const {
      unsigned size = c1.size();
      for (unsigned i = 0; i < size; ++i) if ( c2[i] && !c1[i]) return false;
      return true;
    }
    
    void inference_step(const rule_set& rules, unsigned current_id) {
      func_decl* current_func_decl = m_node2func_decl[current_id];
      func_decl2uints::obj_map_entry* e_current_rules = 
	m_func_decl_body2rules.find_core(current_func_decl);
      if (!e_current_rules) return;
      uint_set& current_rules = e_current_rules->get_data().m_value;
      for (uint_set::iterator r_id = current_rules.begin(),
	     r_id_end = current_rules.end(); r_id != r_id_end; ++r_id) {
	// positions of current_id among body func_decls
	uint_set current_poss;
	rule* r = rules.get_rule(*r_id);
	for (unsigned i = 0; i < r->get_uninterpreted_tail_size(); ++i)
	  if (r->get_decl(i) == current_func_decl) 
	    current_poss.insert(i);
	// create set of combinations of nodes to apply the rule
	vector<node_vector> nodes_set;
	nodes_set.push_back(node_vector());
	// current_id is put on each appropriate position
	for (uint_set::iterator current_pos = current_poss.begin(),
	       current_pos_end = current_poss.end();
	     current_pos != current_pos_end; ++current_pos) {
	  node_set current_pos_singleton;
	  current_pos_singleton.insert(current_id);
	  // grow node combinations as cartesian product with nodes at pos
	  for (unsigned pos = 0; pos < r->get_uninterpreted_tail_size();
	       ++pos) {
	    node_set& pos_nodes =
	      (*current_pos == pos) ? 
	      current_pos_singleton :
	      m_func_decl2max_reach_node_set[r->get_decl(pos)];
	    unsigned orig_nodes_set_size = nodes_set.size();
	    // compute cartesian product
	    // first, store the product with first node in place
	    node_set::iterator pos_node = pos_nodes.begin();
	    for (unsigned nodes_set_offset=0; 
		 nodes_set_offset<orig_nodes_set_size; ++nodes_set_offset) 
	      nodes_set[nodes_set_offset].push_back(*pos_node);
	    ++pos_node;
	    // then, product for rest nodes goes into additional vectors
	    for (node_set::iterator pos_node_end = pos_nodes.end(); 
		 pos_node != pos_node_end; ++pos_node) 
	      for (unsigned nodes_set_offset=0; 
		   nodes_set_offset<orig_nodes_set_size; ++nodes_set_offset) {
		nodes_set.push_back(nodes_set[nodes_set_offset]);
		nodes_set.back().push_back(*pos_node);
	      }
	  }
	}
	// apply rule on each node combination
	for (vector<node_vector>::iterator nodes = nodes_set.begin(),
	       nodes_end = nodes_set.end(); nodes != nodes_end; ++nodes) {
	  optional<unsigned>& added_id =
	    add_node(r->get_decl(), cart_pred_abst_rule(*r_id, *nodes), *r_id,
		     *nodes);
	  if (added_id) check_node_property(rules, *added_id);
	}
      }
    }

    void print_predabst_state() const {
      std::cout << "collected predicates:" << std::endl;
      for (func_decl2vars_preds::iterator it = m_func_decl2vars_preds.begin(),
	     end = m_func_decl2vars_preds.end(); it != end; ++it) {
	std::cout << "preds " << mk_pp(it->m_key, m) << " " <<
	  it->m_value.second->size() << " :"; 
	print_expr_ref_vector(*(it->m_value.second));
      }
      std::cout << "instantiated predicates" << std::endl;
      for (unsigned r_id = 0; r_id < m_rule2gpreds_vector.size(); ++r_id) {
	std::cout << "inst " << r_id << ": " << 
	  mk_pp(m_rule2gbody[r_id], m) << std::endl;
	vector<expr_ref_vector> preds_vector;
	m_rule2gpreds_vector.find(r_id, preds_vector);
	for (unsigned i=0; i < preds_vector.size(); ++i) {
	  std::cout << "  #" << i << "(" << preds_vector[i].size() << "): ";
	  print_expr_ref_vector(preds_vector[i]);
	}
      } 
      std::cout << "rule dependency" << std::endl;
      for (func_decl2uints::iterator it = m_func_decl_body2rules.begin(),
	     end = m_func_decl_body2rules.end(); it != end; ++it) 
	std::cout << mk_pp(it->m_key, m) << ": " << it->m_value << std::endl;
    }

    void print_inference_state() const {
      std::cout << ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>" << 
	std::endl << "m_node_counter " << m_node_counter << std::endl;
      for (unsigned i = 0; i < m_node_counter; ++i) 
	std::cout << "node " << i << " " << 
	  mk_pp(m_node2func_decl[i], m) << " [" << *m_node2cube[i] << "] " << 
	  m_node2parent_rule[i] << " (" << m_node2parent_nodes[i] << ")" << 
	  std::endl;
      for (func_decl2node_set::iterator 
	     it = m_func_decl2max_reach_node_set.begin(),
	     end = m_func_decl2max_reach_node_set.end();
	   it != end; ++it) 
	std::cout << "max reached nodes " << mk_pp(it->m_key, m) 
		  << " " << it->m_value << std::endl;
      std::cout << "worklist " << m_node_worklist << std::endl <<
	"<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<" << std::endl;
    }

    void print_expr_ref_vector(const expr_ref_vector& v, bool newline = true)
      const {
      unsigned size = v.size();
      if (size > 0) {
	std::cout << mk_pp(v[0], m);
	for (unsigned i = 1; i < size; ++i) std::cout << ", " << mk_pp(v[i], m);
      }
      if (newline) std::cout << std::endl;
    }
  };

  predabst::predabst(context& ctx):
    engine_base(ctx.get_manager(), "predabst"),
    m_imp(alloc(imp, ctx)) {        
  }
  predabst::~predabst() {
    dealloc(m_imp);
  }    
  lbool predabst::query(expr* query) {
    return m_imp->query(query);
  }
  void predabst::cancel() {
    m_imp->cancel();
  }
  void predabst::cleanup() {
    m_imp->cleanup();
  }
  void predabst::reset_statistics() {
    m_imp->reset_statistics();
  }
  void predabst::collect_statistics(statistics& st) const {
    m_imp->collect_statistics(st);
  }
  void predabst::display_certificate(std::ostream& out) const {
    m_imp->display_certificate(out);
  }
  expr_ref predabst::get_answer() {
    return m_imp->get_answer();
  }
  model_ref predabst::get_model() {
    return m_imp->get_model();
  }
  /*
  proof_ref predabst::get_proof() {
    std::cout << "predabst get proof" << std::endl;
    throw default_exception("predabst get proof");
    }
  */
};

inline std::ostream& operator<<(std::ostream& out, const vector<bool>& v) {
  unsigned size = v.size();
  if (size > 0) {
    out << v[0];
    for (unsigned i = 1; i < size; ++i) out << "," << v[i];
  }
  return out;
}

inline std::ostream& operator<<(std::ostream& out, const vector<unsigned>& v) {
  unsigned size = v.size();
  if (size > 0) {
    out << v[0];
    for (unsigned i = 1; i < size; ++i) out << "," << v[i];
  }
  return out;
}
