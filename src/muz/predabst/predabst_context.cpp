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

#include <cstring>

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

    // predicate that track abstraction: predix and its size
    static char const * const m_pred_symbol_prefix; 
    static unsigned const m_pred_symbol_prefix_size; 

    typedef obj_map<func_decl, std::pair<expr * const *, expr_ref_vector *> > 
    func_decl2vars_preds;
    func_decl2vars_preds m_func_decl2vars_preds;

    typedef u_map<expr *> id2expr;
    id2expr m_rule2gbody;

    typedef u_map<vector<expr_ref_vector> > id2preds_vector;
    id2preds_vector m_rule2gpreds_vector;

    expr_ref_vector m_empty_preds;

    ast_ref_vector m_ast_trail;

    unsigned m_node_counter;
    typedef vector<bool> cube_t;

    typedef u_map<func_decl *> node2func_decl;
    node2func_decl m_node2func_decl;

    typedef u_map<cube_t> node2cube;
    node2cube m_node2cube;

    typedef vector<unsigned> node_vector;
    typedef uint_set node_set;

    typedef u_map<unsigned> node2rule;
    node2rule m_node2parent_rule;

    typedef u_map<node_vector> node2nodes;
    node2nodes m_node2parent_nodes;

    typedef obj_map<func_decl, uint_set > func_decl2node_set;
    func_decl2node_set m_func_decl2max_reach_node_set;

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
    }        

    lbool query(expr* query) {
      m_ctx.ensure_opened();

      datalog::rule_set & rules = m_ctx.get_rules();

      std::cout << "begin original rules\n";
      rules.display(std::cout);
      std::cout << "end original rules\n";

      // collect predicates and delete corresponding rules
      for (rule_set::iterator rules_it = rules.begin(), rules_end = rules.end();
	   rules_it != rules_end; ++rules_it) {
	rule * r = *rules_it;
	func_decl * head_decl = r->get_decl();
	char const * head_str = head_decl->get_name().bare_str();

	if (r->get_uninterpreted_tail_size() != 0 
	    || memcmp(head_str, m_pred_symbol_prefix, m_pred_symbol_prefix_size)
	    ) {
	  continue; 
	}
	// create func_decl from suffix and map it to predicates
	unsigned suffix_size = strlen(head_str)-m_pred_symbol_prefix_size;
	char * suffix = new char[suffix_size+1];
#ifdef _WINDOWS
	strcpy_s(suffix, suffix_size+1, &head_str[m_pred_symbol_prefix_size]); 
#else   // strncpy_s is not available outside Windows
	strncpy(suffix, &head_str[m_pred_symbol_prefix_size], suffix_size+1);
#endif
	func_decl * suffix_decl = 
	  m.mk_func_decl(symbol(suffix), head_decl->get_arity(), 
			 head_decl->get_domain(), head_decl->get_range());
	m_ast_trail.push_back(suffix_decl);
	// add predicates to m_func_decl2vars_preds
	expr_ref_vector * preds = alloc(expr_ref_vector, m);
	preds->reserve(r->get_tail_size());
	for (unsigned i = 0; i < r->get_tail_size(); ++i) 
	  (*preds)[i] = r->get_tail(i);
	m_func_decl2vars_preds.
	  insert(suffix_decl, std::make_pair(r->get_head()->get_args(), preds));
	// rule is not used for inference
	rules.del_rule(r);
      }

      std::cout << "collected predicates:" << std::endl;
      for (func_decl2vars_preds::iterator it = m_func_decl2vars_preds.begin(),
	     end = m_func_decl2vars_preds.end(); it != end; ++it) {
	std::cout << "preds " << mk_pp(it->m_key, m) << ":"; 
	print_expr_ref_vector(*(it->m_value.second));
	std::cout << std::endl;
      } 

      std::cout << "remaining rules "<< rules.get_num_rules() << std::endl;
      rules.display(std::cout);

      // for each rule: ground body and instantiate predicates for applications
      for (unsigned r_id = 0; r_id < rules.get_num_rules(); ++r_id) {
	rule * r = rules.get_rule(r_id);
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
	for (unsigned i=r->get_uninterpreted_tail_size(); 
	     i<r->get_tail_size(); ++i)
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
	for (unsigned i=0; i<r->get_uninterpreted_tail_size(); ++i) 
	  gpreds_vector.push_back(app_inst_preds(r->get_tail(i), rule_subst));
	// store instantiation for non-query head
	if (!rules.is_output_predicate(r->get_decl())) {
	  expr_ref_vector hpreds = app_inst_preds(r->get_head(), rule_subst);
	  expr_ref_vector npreds(m);
	  npreds.reserve(hpreds.size());
	  for (unsigned i=0; i<hpreds.size(); ++i) 
	    npreds[i] = m.mk_not(hpreds[i].get());
	  gpreds_vector.push_back(npreds);
	}
	m_rule2gpreds_vector.insert(r_id, gpreds_vector);
      }

      std::cout << "instantiated predicates" << std::endl;
      for (unsigned r_id=0; r_id<m_rule2gpreds_vector.size(); ++r_id) {
	rules.get_rule(r_id)->display(m_ctx, std::cout);
	std::cout << "inst " << r_id << ": " << 
	  mk_pp(m_rule2gbody.find_core(r_id)->get_data().m_value, m) << 
	  std::endl;
	vector<expr_ref_vector> preds_vector;
	m_rule2gpreds_vector.find(r_id, preds_vector);
	for (unsigned i=0; i<preds_vector.size(); ++i) {
	  std::cout << "  #" << i << "(" << preds_vector[i].size() << "): ";
	  print_expr_ref_vector(preds_vector[i]);
	  std::cout << std::endl;
	}
      } 

      // initial abstract inference
      for (unsigned r_id=0; r_id<rules.get_num_rules(); ++r_id) {
	rule * r = rules.get_rule(r_id);
	if (r->get_uninterpreted_tail_size() != 0) continue;
	cube_t const & cube = cart_pred_abst_rule(r_id);
        std::cout << "cube ";
        print_cube(cube);
        std::cout << std::endl;
	add_cube(r->get_decl(), cube, r_id);
      }
      print_inference_state();
      return l_true;
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
      expr_ref ans = get_answer();
      out << mk_pp(ans, m) << "\n";    
    }

    expr_ref get_answer() const {
      // TBD hmm?
      return expr_ref(m.mk_true(), m);
    }

  private:
    // ground arguments of app using subst, and then instantiate each predicate
    // by replacing its free variables with grounded arguments of app
    expr_ref_vector app_inst_preds(app * appl, expr_ref_vector const & subst) {
      func_decl2vars_preds::obj_map_entry * e = 
	m_func_decl2vars_preds.find_core(appl->get_decl());
      if (!e) return m_empty_preds;
      expr * const * vars = e->get_data().get_value().first;
      expr_ref_vector const & preds = *e->get_data().get_value().second;
      std::cout << "start app_inst_preds" << std::endl;
      std::cout << "app " << mk_pp(appl, m) << std::endl;
      std::cout << "vars ";
      for (unsigned i=0; i<appl->get_num_args(); ++i)
	std::cout << mk_pp(vars[i], m);
      std::cout << std::endl << "preds " << preds.size() << " ";
      print_expr_ref_vector(preds);
      std::cout << std::endl;
      // ground appl arguments
      expr_ref subst_tmp(m);
      m_var_subst(appl, subst.size(), subst.c_ptr(), subst_tmp);
      std::cout << "ground appl " << mk_pp(subst_tmp, m) << std::endl;
      // instantiation maps preds variables to head arguments
      expr_ref_vector inst(m);
      inst.reserve(appl->get_num_args());
      app * gappl = to_app(subst_tmp);
      for (unsigned i=0; i<appl->get_num_args(); ++i) {
	unsigned idx = to_var(vars[i])->get_idx();
	if (idx>=inst.size())
	  inst.resize(idx+1);
	inst[idx] = gappl->get_arg(i);
      }
      std::cout << "inst " << inst.size() << " ";
      print_expr_ref_vector(inst);
      std::cout << std::endl;
      // preds instantiates to inst_preds
      expr_ref_vector inst_preds(m);
      inst_preds.reserve(preds.size());
      for (unsigned i=0; i<preds.size(); ++i) {	      
	m_var_subst(preds[i], inst.size(), inst.c_ptr(), subst_tmp);
	inst_preds[i] = subst_tmp;
      }
      return inst_preds;
    }
    
    cube_t cart_pred_abst_rule(unsigned r_id, 
			       node_vector const & nodes = node_vector()) {
      cube_t cube;
      std::cout << "pred_abst_rule " << r_id << std::endl;
      // get instantiated predicates
      vector<expr_ref_vector> preds_vector = 
	m_rule2gpreds_vector.find_core(r_id)->get_data().m_value;
      // TODO load abstract states for nodes
      expr_ref_vector head_preds = preds_vector.back();
      if (head_preds.empty()) return cube;
      m_solver.push();
      m_solver.assert_expr(m_rule2gbody.find_core(r_id)->get_data().m_value);
      // collect abstract cube
      cube.resize(head_preds.size());
      for (unsigned i=0; i<head_preds.size(); ++i) {
	m_solver.push();
	m_solver.assert_expr(head_preds[i].get());
	cube[i] = (m_solver.check() == l_false);
	m_solver.pop(1);
      }
      m_solver.pop(1);
      return cube;
    }

    bool add_cube(func_decl * sym, cube_t const & cube, 
		  unsigned r_id, node_vector const & nodes = node_vector()) {
      func_decl2node_set::obj_map_entry * sym_nodes_entry =
	m_func_decl2max_reach_node_set.find_core(sym);
      if (sym_nodes_entry) { 
	// nodes exist at this sym
	node_set & sym_nodes = sym_nodes_entry->get_data().m_value;
	node_vector old_lt_nodes;
	for (uint_set::iterator it = sym_nodes.begin(), end = sym_nodes.end();
	     it != end; ++it) {
	  cube_t const & old_cube =
	    m_node2cube.find_core(*it)->get_data().m_value;
	  // if cube implies existing cube then nothing to add
	  if (cube_leq(cube, old_cube)) return false;
	  // stronger old cubes will not be considered maximal
	  if (cube_leq(old_cube, cube)) old_lt_nodes.push_back(*it);
	}
	// remove subsumed, previously maximal cubes
	for (node_vector::iterator it = old_lt_nodes.begin(), 
	       end = old_lt_nodes.end(); it != end; ++it)
	  sym_nodes.remove(*it);
	sym_nodes.insert(m_node_counter);
      } else {
	node_set sym_nodes;
	sym_nodes.insert(m_node_counter);
	m_func_decl2max_reach_node_set.insert(sym, sym_nodes);
      }
      m_node2func_decl.insert(m_node_counter, sym);
      m_node2cube.insert(m_node_counter, cube);
      m_node2parent_rule.insert(m_node_counter, r_id);
      m_node2parent_nodes.insert(m_node_counter, nodes);
      m_node_counter++;
      return true;
    }

    // return whether c1 implies c2
    bool cube_leq(cube_t const & c1, cube_t const & c2) {
      unsigned size = c1.size();
      for (unsigned i=0; i<size; ++i) 
	if ( c2[i] && !c1[i]) return false;
      return true;
    }

    void print_inference_state() {
      printf("m_node_counter %d\n", m_node_counter);
      for (unsigned i=0; i<m_node_counter; ++i) {
	std::cout << "node " << i << " " <<
	  mk_pp(m_node2func_decl.find_core(i)->get_data().m_value, m) << " [";
	print_cube(m_node2cube.find_core(i)->get_data().m_value);
	std::cout << "] " << 
	  m_node2parent_rule.find_core(i)->get_data().m_value << " (";
	node_vector const & parent_nodes = 
	  m_node2parent_nodes.find_core(i)->get_data().m_value;
	for (unsigned j=0; j<parent_nodes.size(); ++j) {
	  std::cout << j;
	  if (j<parent_nodes.size()-1) std::cout << ", ";
	}
	std::cout << ")" << std::endl;
      }
      for (func_decl2node_set::iterator 
	     it = m_func_decl2max_reach_node_set.begin(),
	     end = m_func_decl2max_reach_node_set.end();
	   it != end; ++it) 
	std::cout << "max reached nodes " << mk_pp(it->m_key, m) 
		  << " " << it->m_value << std::endl;
    }

    void print_cube(cube_t const & c) {
      for (unsigned i=0; i<c.size(); ++i) {
        std::cout << i;
        if (i<c.size()-1) std::cout << ", ";
      }
    }

    void print_expr_ref_vector(expr_ref_vector const & v) {
      unsigned size = v.size();
      for (unsigned i = 0; i < size; ++i) {
	std::cout << mk_pp(v[i], m);
	if (i < size-1) std::cout << ", ";
      }
    }

    void print_expr_ref_vector(expr_ref_vector * v) {
      unsigned size = v->size();
      for (unsigned i = 0; i < size; ++i) {
	std::cout << mk_pp((*v)[i].get(), m);
	if (i < size-1) std::cout << ", ";
      }
    }
  };

  char const * const predabst::imp::m_pred_symbol_prefix = "__pred__";
  unsigned const predabst::imp::m_pred_symbol_prefix_size = strlen(m_pred_symbol_prefix);
    
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

};
