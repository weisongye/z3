/*++
  Copyright (c) 2013 Microsoft Corporation

  Module Name:

  predabst_context.cpp

  Abstract:

  Bounded PREDABST (symbolic simulation using Z3) context.

  Author:

  Modified by Andrey Rybalchenko (rybal) 2014-3-7.

  Revision History:

--*/

#include "farkas_util.h"
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

    struct rule_info {
      expr_ref                m_body;
      vector<expr_ref_vector> m_preds;
      rule_info(expr_ref& body): m_body(body) {}
    };

    class scoped_push {
        smt::kernel& s;
    public:
        scoped_push(smt::kernel& s):s(s){ s.push();  }
        ~scoped_push() { s.pop(1); }
    };

    
    context&               m_ctx;         // main context where (fixedpoint) constraints are stored.
    ast_manager&           m;             // manager for ASTs. It is used for managing expressions
    rule_manager&          rm;            // context with utilities for fixedpoint rules.
    smt_params             m_fparams;     // parameters specific to smt solving
    smt::kernel            m_solver;      // basic SMT solver class
    var_subst              m_var_subst;   // substitution object. It gets updated and reset.
    volatile bool          m_cancel;      // Boolean flag to track external cancelation.
    stats                  m_stats;       // statistics information specific to the CLP module.

    typedef obj_map<func_decl, std::pair<expr* const*, expr_ref_vector*> > 
    func_decl2vars_preds;
    func_decl2vars_preds m_func_decl2vars_preds;

    vector<rule_info> m_rule2info;

    typedef obj_map<func_decl, uint_set> func_decl2uints;
    func_decl2uints m_func_decl_body2rules;

    expr_ref_vector m_empty_preds;
    ast_ref_vector  m_ast_trail;

    typedef vector<bool> cube_t;
    typedef vector<unsigned> node_vector;
    struct node_info {
      func_decl*  m_func_decl;
      cube_t      m_cube;
      unsigned    m_parent_rule;
      node_vector m_parent_nodes;
      node_info() {}
      node_info(func_decl* f, cube_t& c, unsigned r, node_vector n):
	m_func_decl(f),
	m_cube(c),
	m_parent_rule(r),
	m_parent_nodes(n)
      {}
    };
    typedef uint_set node_set;
    typedef obj_map<func_decl, node_set> func_decl2node_set;

    vector<node_info>  m_node2info;                        
    func_decl2node_set m_func_decl2max_reach_node_set;    
    node_set           m_node_worklist;                    

  public:
    imp(context& ctx):
      m_ctx(ctx), 
      m(ctx.get_manager()),
      rm(ctx.get_rule_manager()),
      m_solver(m, m_fparams),  
      m_var_subst(m, false),
      m_cancel(false),
      m_empty_preds(m),
      m_ast_trail(m)
    {
      // m_fparams.m_relevancy_lvl = 0;
      m_fparams.m_mbqi = false;
      m_fparams.m_soft_timeout = 1000;
    }

    ~imp() {
      for (func_decl2vars_preds::iterator it = m_func_decl2vars_preds.begin(), 
	     end = m_func_decl2vars_preds.end(); it != end; ++it) 
	dealloc(it->m_value.second);
    }        

    lbool query(expr* query) {
      m_ctx.ensure_opened();
      rule_set& rules = m_ctx.get_rules();
      rm.mk_query(query, rules);
      ptr_vector<rule> to_delete;
      try {
        // collect predicates and delete corresponding rules
        for (unsigned i = 0; !m_cancel && i < rules.get_num_rules(); ++i)
          collect_predicates(rules, i, to_delete);
        for (unsigned i = 0; !m_cancel && i < to_delete.size(); ++i) 
          rules.del_rule(to_delete[i]);
        // for each rule: ground body and instantiate predicates for applications
        for (unsigned i = 0; !m_cancel && i < rules.get_num_rules(); ++i)
	  instantiate_rule(rules, i);
	// initial abstract inference
	for (unsigned i = 0; !m_cancel && i < rules.get_num_rules(); ++i)
          initialize_abs(rules, i);	
	// process worklist
	while (!m_cancel && !m_node_worklist.empty()) {
          TRACE("dl", print_inference_state(tout););
	  unsigned current_id = *m_node_worklist.begin();
	  m_node_worklist.remove(current_id);
	  inference_step(rules, current_id);
	}
      } catch (reached_query& exc) {
	print_proof_prolog(std::cout, exc.m_node);
	return l_true;
      }
      if (m_cancel) return l_undef;
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
        expr_ref_vector disj(m);
	if (e) {
	  expr_ref_vector const& preds = *e->get_data().get_value().second;
	  for (node_set::iterator it_node = it_decl->m_value.begin(),
		 end_node = it_decl->m_value.end(); it_node != end_node;
	       ++it_node) {
	    cube_t const& cube = m_node2info[*it_node].m_cube;
            expr_ref_vector conj(m);
	    for (unsigned i = 0; i < cube.size(); ++i) 
                if (cube[i]) conj.push_back(preds[i]);
            disj.push_back(m.mk_and(conj.size(), conj.c_ptr()));
	  }
	} else {
            disj.push_back(m.mk_true());
	}
	func_interp* fi = alloc(func_interp, m, it_decl->m_key->get_arity());
	fi->set_else(m.mk_or(disj.size(), disj.c_ptr()));
	md->register_decl(it_decl->m_key, fi);
      }
      func_decl_set false_func_decls;
      // unreachable body predicates are false
      for (func_decl2uints::iterator it = m_func_decl_body2rules.begin(),
	     end = m_func_decl_body2rules.end(); it != end; ++it) {
	if (!m_func_decl2max_reach_node_set.contains(it->m_key)) 
	  false_func_decls.insert(it->m_key);
      }
      // unreachable head predicates are false
      rule_set& rules = m_ctx.get_rules();
      for (rule_set::iterator it = rules.begin(), end = rules.end(); it != end;
	   ++it) {
	func_decl* head_decl = (*it)->get_decl();
	if (rules.is_output_predicate(head_decl)) continue;
	if (!m_func_decl2max_reach_node_set.contains(head_decl)) 
	  false_func_decls.insert(head_decl);
      }
      for (func_decl_set::iterator it = false_func_decls.begin(),
	     end = false_func_decls.end(); it != end; ++it) {
        func_decl* d = *it;
        if (d->get_arity() == 0) {
          md->register_decl(d, m.mk_false());
        }
        else {
          func_interp* fi = alloc(func_interp, m, d->get_arity());
          fi->set_else(m.mk_false());
          md->register_decl(d, fi);
        }
      }
      return md;
    }

  private:

    void initialize_abs(rule_set const& rules, unsigned r_id) {
       rule* r = rules.get_rule(r_id);
       cube_t cube;
       if (r->get_uninterpreted_tail_size() == 0 && 
           cart_pred_abst_rule(r_id, cube))
         check_node_property(rules,
                             add_node(r->get_decl(),
                                      cube,
                                      r_id));

    }

    void instantiate_rule(rule_set const& rules, unsigned r_id) {
      rule* r = rules.get_rule(r_id);
      // prepare grounding substitution
      ptr_vector<sort> free_sorts;
      r->get_vars(m, free_sorts);
      expr_ref_vector rule_subst(m);
      rule_subst.reserve(free_sorts.size());
      for (unsigned i = 0; i < rule_subst.size(); ++i) 
	rule_subst[i] = m.mk_fresh_const("c", free_sorts[i]);
      // conjoin constraints in rule body
      unsigned usz = r->get_uninterpreted_tail_size();
      unsigned tsz = r->get_tail_size();
      expr_ref conj(m.mk_and(tsz - usz, r->get_expr_tail() + usz), m);
      // apply substitution
      m_var_subst(conj, rule_subst.size(), rule_subst.c_ptr(), conj);
      // store ground body and instantiations
      rule_info info(conj);              
      vector<expr_ref_vector>& preds = info.m_preds;
      // store instantiation for body applications
      for (unsigned i = 0; i < usz; ++i) {
	preds.push_back(expr_ref_vector(m));
	app_inst_preds(r->get_tail(i), rule_subst, preds[i]);
      }
      // store instantiation for non-query head
      if (!rules.is_output_predicate(r->get_decl())) {
	expr_ref_vector heads(m);
	app_inst_preds(r->get_head(), rule_subst, heads);
	for (unsigned i = 0; i < heads.size(); ++i) 
	  heads[i] = m.mk_not(heads[i].get());
	preds.push_back(heads);
      }
      m_rule2info.push_back(info);
      // map body func_decls to rule
      for (unsigned i = 0; i < usz; ++i)
	m_func_decl_body2rules.
	  insert_if_not_there2(r->get_decl(i), uint_set())->
	  get_data().m_value.insert(r_id);
    }
    
    void collect_predicates(rule_set& rules, unsigned r_id, ptr_vector<rule>& to_delete) {          
      rule* r = rules.get_rule(r_id);
      if (!is_pred_abst(r)) return;
      func_decl* head_decl = r->get_decl();
      symbol suffix(head_decl->get_name().str().substr(8).c_str());
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
      to_delete.push_back(r);
    }
    
    bool is_pred_abst(rule *r) const {
      return r->get_uninterpreted_tail_size() == 0 &&
	r->get_decl()->get_name().str().substr(0, 8) == "__pred__";
    }

    void print_proof_prolog(std::ostream& out, unsigned id) const {
      node_set todo_nodes;
      todo_nodes.insert(id);
      while (!todo_nodes.empty()) {
	unsigned curr_id = *todo_nodes.begin();
	todo_nodes.remove(curr_id);
	node_info const& node = m_node2info[curr_id];
	out << "hyper_resolve([" << node.m_parent_nodes << "], " <<
	  node.m_parent_rule << ", " << curr_id << ")." << std::endl;
	for (unsigned i = 0; i < node.m_parent_nodes.size(); ++i)
	  todo_nodes.insert(node.m_parent_nodes[i]);
      }
    }

    static const unsigned NON_NODE = UINT_MAX;

    struct reached_query {
      unsigned m_node;
      reached_query(unsigned node): m_node(node) {}
    };
    
    // ground arguments of app using subst, and then instantiate each predicate
    // by replacing its free variables with grounded arguments of app
    void app_inst_preds(app* appl, expr_ref_vector const& subst,
			expr_ref_vector& inst_preds) {      
        
      func_decl2vars_preds::obj_map_entry* e = 
	m_func_decl2vars_preds.find_core(appl->get_decl());
      if (!e) return;
      expr* const* vars = e->get_data().get_value().first;
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
      inst_preds.reserve(preds.size());
      for (unsigned i = 0; i < preds.size(); ++i) {
	m_var_subst(preds[i].get(), inst.size(), inst.c_ptr(), subst_tmp);
	inst_preds[i] = subst_tmp;
      }
    }

    
   bool cart_pred_abst_rule(unsigned r_id, 
                             cube_t& cube,
                             node_vector const& nodes = node_vector()) {
      // get instantiated predicates
      vector<expr_ref_vector> const& preds_vector = m_rule2info[r_id].m_preds;
      scoped_push _push1(m_solver);
      m_solver.assert_expr(m_rule2info[r_id].m_body);
      // load abstract states for nodes
      for (unsigned pos = 0; pos < nodes.size(); ++pos) {
	cube_t& pos_cube = m_node2info[nodes[pos]].m_cube;
	for (unsigned i = 0; i < preds_vector[pos].size(); ++i) 
	  if (pos_cube[i]) m_solver.assert_expr(preds_vector[pos][i]);
      }
      if (m_solver.check() == l_false) {
	// unsat body
        return false; 
      }
      // collect abstract cube
      expr_ref_vector const& head_preds = preds_vector.back();
      cube.resize(head_preds.size());
      for (unsigned i = 0; i < head_preds.size(); ++i) {
        scoped_push _push2(m_solver);
	m_solver.assert_expr(head_preds[i]);
	cube[i] = (m_solver.check() == l_false);
      }
      return true;
    }

    unsigned add_node(func_decl* sym, cube_t& cube, 
		      unsigned r_id, node_vector const& nodes = node_vector()) {
      unsigned added_id = m_node2info.size();
      func_decl2node_set::obj_map_entry * sym_nodes_entry =
	m_func_decl2max_reach_node_set.find_core(sym);
      // first fixpoint check combined with maximality maintainance
      if (sym_nodes_entry) { 
	// nodes exist at this sym
	node_set& sym_nodes = sym_nodes_entry->get_data().m_value;
	node_vector old_lt_nodes;
	for (node_set::iterator it = sym_nodes.begin(), end = sym_nodes.end();
	     it != end; ++it) {
	  cube_t& old_cube = m_node2info[*it].m_cube;
	  // if cube implies existing cube then nothing to add
	  if (cube_leq(cube, old_cube)) {
	    return NON_NODE;
	  }
	  // stronger old cubes will not be considered maximal
	  if (cube_leq(old_cube, cube)) old_lt_nodes.push_back(*it);
	}
	// fixpoint reached since didn't return
	// remove subsumed maximal nodes
	for (node_vector::iterator it = old_lt_nodes.begin(), 
	       end = old_lt_nodes.end(); it != end; ++it) {
	  sym_nodes.remove(*it);
	  m_node_worklist.remove(*it); // removing non-existent element is ok
	}
	sym_nodes.insert(added_id);
      } else {
	m_func_decl2max_reach_node_set.insert_if_not_there2(sym, node_set())->
	  get_data().m_value.insert(added_id);
      }
      // no fixpoint reached hence create new node
      m_node_worklist.insert(added_id);
      m_node2info.push_back(node_info(sym, cube, r_id, nodes));
      return added_id;
    }



	void check_node_property(rule_set const& rules, unsigned id) const {
		if (id != NON_NODE && rules.is_output_predicate(m_node2info[id].m_func_decl)) 
			throw reached_query(id);
		if (id != NON_NODE && is_wf_predicate(m_node2info[id].m_func_decl)) {
			check_well_founded(id);
		}
	}

	bool is_wf_predicate(func_decl * pred) const {
		return pred->get_name().str().substr(0, 6) == "__wf__";
	}

	void check_well_founded(unsigned r_id) const {
		func_decl * pred = m_node2info[r_id].m_func_decl;
		cube_t cube = m_node2info[r_id].m_cube;
		func_decl2vars_preds::obj_map_entry* e = m_func_decl2vars_preds.find_core(pred);
		if (!e) return;
		expr* const* vars = e->get_data().get_value().first;
		expr_ref_vector preds_set = *(e->get_data().get_value().second);
		expr_ref_vector cube_preds_set(m);
		for (unsigned i = 0; i < cube.size(); i++) {
			if (cube[i]) cube_preds_set.push_back(preds_set[i].get());
		}
		expr_ref to_rank(m.mk_and(cube_preds_set.size(), cube_preds_set.c_ptr()), m);
		//std::cout << "to_rank: " << mk_pp(to_rank, m) << "\n";		
		
		expr_ref_vector values(m);
		expr_ref bound(m), decrease(m);
		if (well_founded(expr_ref_vector(m, (pred->get_arity()), vars), to_rank, bound, decrease)) {
			std::cout << "===================================== \n";
			std::cout << "Formula is well-founded! \n";
			std::cout << "===================================== \n";
			std::cout << "bound: " << mk_pp(bound, m) << "\n";
			std::cout << "decrease: " << mk_pp(decrease, m) << "\n";

		}
		else{
			std::cout << "===================================== \n";
			std::cout << "Formula is not well-founded! \n";
			std::cout << "===================================== \n";
			throw reached_query(r_id);
		}
	}
    
    // return whether c1 implies c2
    bool cube_leq(cube_t const& c1, cube_t const& c2) const {
      unsigned size = c1.size();
      for (unsigned i = 0; i < size; ++i) if ( c2[i] && !c1[i]) return false;
      return true;
    }
    
    void inference_step(rule_set const& rules, unsigned current_id) {
      func_decl* current_func_decl = m_node2info[current_id].m_func_decl;
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
            cube_t cube;
            if (cart_pred_abst_rule(*r_id, cube, *nodes))
                check_node_property(rules,
                                    add_node(r->get_decl(),
                                             cube,
                                             *r_id, *nodes));
        }
      }
    }

    void print_predabst_state(std::ostream& out) const {
      out << "collected predicates:" << std::endl;
      for (func_decl2vars_preds::iterator it = m_func_decl2vars_preds.begin(),
	     end = m_func_decl2vars_preds.end(); it != end; ++it) {
	out << "preds " << mk_pp(it->m_key, m) << " " <<
	  it->m_value.second->size() << " :"; 
	print_expr_ref_vector(out, *(it->m_value.second));
      }
      out << "instantiated predicates" << std::endl;
      for (unsigned r_id = 0; r_id < m_rule2info.size(); ++r_id) {
	out << "inst " << r_id << ": " << 
	  mk_pp(m_rule2info[r_id].m_body, m) << std::endl;
	vector<expr_ref_vector> const& preds_vector = m_rule2info[r_id].m_preds;
	for (unsigned i = 0; i < preds_vector.size(); ++i) {
	  out << "  #" << i << "(" << preds_vector[i].size() << "): ";
	  print_expr_ref_vector(out, preds_vector[i]);
	}
      } 
      out << "rule dependency" << std::endl;
      for (func_decl2uints::iterator it = m_func_decl_body2rules.begin(),
	     end = m_func_decl_body2rules.end(); it != end; ++it) {
	out << mk_pp(it->m_key, m) << ": " << it->m_value << std::endl;
      }
    }
    
    
    void print_inference_state(std::ostream& out) const {
      out << ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>" <<
	std::endl << "node counter " << m_node2info.size() << std::endl;
      for (unsigned i = 0; i < m_node2info.size(); ++i) {
	node_info const& node = m_node2info[i];
	out << "node " << i << " " << 
	  mk_pp(node.m_func_decl, m) << " [" << node.m_cube << "] " << 
	  node.m_parent_rule << " (" << node.m_parent_nodes << ")" <<
	  std::endl;
      }
      for (func_decl2node_set::iterator 
	     it = m_func_decl2max_reach_node_set.begin(),
	     end = m_func_decl2max_reach_node_set.end();
	   it != end; ++it) 
	out << "max reached nodes " << mk_pp(it->m_key, m) << " " <<
	  it->m_value << std::endl;
      out << "worklist " << m_node_worklist << std::endl <<
	"<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<" << std::endl;
    }
    
    void print_expr_ref_vector(std::ostream& out, expr_ref_vector const& v,
			       bool newline = true) const {
      for (unsigned i = 0; i < v.size(); ++i) {
	out << mk_pp(v[i], m);
	if (i + 1 < v.size()) out << ", ";
      }
      if (newline) out << std::endl;
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

template<class T>
inline std::ostream& operator<<(std::ostream& out, const vector<T>& v) {
  unsigned size = v.size();
  if (size > 0) {
    out << v[0];
    for (unsigned i = 1; i < size; ++i) out << "," << v[i];
  }
  return out;
}