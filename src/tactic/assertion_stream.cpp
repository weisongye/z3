/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    assertion_stream.cpp

Abstract:

    Abstract wrapper for assertion_stacks and goals.
    It allows us to build procedures that operate on
    both of them.

Author:

    Leonardo de Moura (leonardo) 2012-12-13

Revision History:

*/
#include<iomanip>
#include"assertion_stream.h"
#include"goal.h"
#include"assertion_stack.h"
#include"extension_model_converter.h"
#include"filter_model_converter.h"
#include"macro_substitution.h"
#include"stopwatch.h"
#include"tactic.h"

assertion_stream::~assertion_stream() {
}

assertion_stack2stream::assertion_stack2stream(assertion_stack & s):
m_stack(s) {
}

assertion_stack2stream::~assertion_stack2stream() {
}

bool assertion_stack2stream::is_frozen(func_decl * f) const {
    return m_stack.is_frozen(f);
}
    
ast_manager & assertion_stack2stream::m() const {
    return m_stack.m();
}
    
bool assertion_stack2stream::models_enabled() const {
    return m_stack.models_enabled();
}

bool assertion_stack2stream::proofs_enabled() const {
    return m_stack.proofs_enabled();
}

bool assertion_stack2stream::unsat_core_enabled() const {
    return m_stack.unsat_core_enabled();
}

bool assertion_stack2stream::inconsistent() const {
    return m_stack.inconsistent();
}

void assertion_stack2stream::inc_depth() {
    // do nothing
}
    
unsigned assertion_stack2stream::qhead() const {
    return m_stack.qhead();
}

unsigned assertion_stack2stream::size() const {
    return m_stack.size();
}

unsigned assertion_stack2stream::num_exprs() const {
    return m_stack.num_exprs();
}
    
void assertion_stack2stream::assert_expr(expr * f, proof * pr, expr_dependency * d) {
    m_stack.assert_expr(f, pr, d);
}

void assertion_stack2stream::assert_expr(expr * f) {
    m_stack.assert_expr(f);
}

void assertion_stack2stream::reset_after_qhead() {
    m_stack.reset_after_qhead();
}
    
expr * assertion_stack2stream::form(unsigned i) const {
    return m_stack.form(i);
}

proof * assertion_stack2stream::pr(unsigned i) const {
    return m_stack.pr(i);
}

expr_dependency * assertion_stack2stream::dep(unsigned i) const {
    return m_stack.dep(i);
}

void assertion_stack2stream::update(unsigned i, expr * f, proof * pr, expr_dependency * dep) {
    m_stack.update(i, f, pr, dep);
}

bool assertion_stack2stream::is_well_sorted() const {
    return m_stack.is_well_sorted();
}

void assertion_stack2stream::add_filter(func_decl * f) {
    m_stack.add_filter(f);
}

void assertion_stack2stream::add_definition(app * c, expr * def, proof * pr, expr_dependency * dep) {
    m_stack.add_definition(c, def, pr, dep);
}

void assertion_stack2stream::add_definition(func_decl * f, quantifier * q, proof * pr, expr_dependency * dep) {
    m_stack.add_definition(f, q, pr, dep);
}

void assertion_stack2stream::elim_redundancies() {
    m_stack.elim_redundancies();
}

void assertion_stack2stream::elim_true() {
    m_stack.elim_true();
}

void assertion_stack2stream::display(std::ostream & out) {
    m_stack.display(out);
}

goal2stream::goal2stream(goal & g):
m_goal(g) {
}

goal2stream::~goal2stream() {
}

bool goal2stream::is_frozen(func_decl * f) const {
    return false;
}

ast_manager & goal2stream::m() const {
    return m_goal.m();
}

bool goal2stream::models_enabled() const {
    return m_goal.models_enabled();
}

bool goal2stream::proofs_enabled() const {
    return m_goal.proofs_enabled();
}

bool goal2stream::unsat_core_enabled() const {
    return m_goal.unsat_core_enabled();
}

bool goal2stream::inconsistent() const {
    return m_goal.inconsistent();
}

void goal2stream::inc_depth() {
    m_goal.inc_depth();
}
    
unsigned goal2stream::qhead() const {
    return 0;
}

unsigned goal2stream::size() const {
    return m_goal.size();
}

unsigned goal2stream::num_exprs() const {
    return m_goal.num_exprs();
}
   
void goal2stream::assert_expr(expr * f, proof * pr, expr_dependency * d) {
    m_goal.assert_expr(f, pr, d);
}

void goal2stream::assert_expr(expr * f) {
    m_goal.assert_expr(f);
}

void goal2stream::reset_after_qhead() {
    m_goal.reset();
}
    
expr * goal2stream::form(unsigned i) const {
    return m_goal.form(i);
}

proof * goal2stream::pr(unsigned i) const {
    return m_goal.pr(i);
}

expr_dependency * goal2stream::dep(unsigned i) const {
    return m_goal.dep(i);
}

void goal2stream::update(unsigned i, expr * f, proof * pr, expr_dependency * dep) {
    m_goal.update(i, f, pr, dep);
}
    
bool goal2stream::is_well_sorted() const {
    return m_goal.is_well_sorted();
}

void goal2stream::add_filter(func_decl * f) {
    UNREACHABLE();
    // goal2stream does not support add_filter, goal_and_fmc2stream should be used instead
}

void goal2stream::add_definition(app * c, expr * def, proof * pr, expr_dependency * dep) {
    UNREACHABLE();
    // goal2stream does not support add_definition, goal_and_emc2stream should be used instead
}

void goal2stream::add_definition(func_decl * f, quantifier * q, proof * pr, expr_dependency * dep) {
    UNREACHABLE();
    // goal2stream does not support add_definition, goal_and_emc2stream should be used instead
}

void goal2stream::elim_redundancies() {
    m_goal.elim_redundancies();
}

void goal2stream::elim_true() {
    m_goal.elim_true();
}

void goal2stream::display(std::ostream & out) {
    m_goal.display(out);
}

goal_and_emc2stream::goal_and_emc2stream(goal & g):
goal2stream(g) {
}

goal_and_emc2stream::~goal_and_emc2stream() {
}

void goal_and_emc2stream::add_definition(app * c, expr * def, proof * pr, expr_dependency * dep) {
    if (!m_mc)
        m_mc = alloc(extension_model_converter, m_goal.m());
    m_mc->insert(c->get_decl(), def);
}

void goal_and_emc2stream::add_definition(func_decl * f, quantifier * q, proof * pr, expr_dependency * dep) {
    if (!m_mc)
        m_mc = alloc(extension_model_converter, m_goal.m());
    app * head; expr * def = 0;
    get_macro_head_def(m(), q, f, head, def);
    SASSERT(def);
    m_mc->insert(f, def);
}

goal_and_fmc2stream::goal_and_fmc2stream(goal & g):
goal2stream(g) {
}

goal_and_fmc2stream::~goal_and_fmc2stream() {
}

void goal_and_fmc2stream::add_filter(func_decl * f) {
    if (!m_mc)
        m_mc = alloc(filter_model_converter, m_goal.m());
    m_mc->insert(f);
}

struct stream_report::imp {
    char const *              m_id;
    assertion_stream const &  m_stack;
    stopwatch                 m_watch;
    double                    m_start_memory;

    imp(char const * id, assertion_stream const & s):
        m_id(id),
        m_stack(s),
        m_start_memory(static_cast<double>(memory::get_allocation_size())/static_cast<double>(1024*1024)) {
        m_watch.start();
    }
        
    ~imp() {
        m_watch.stop();
        double end_memory = static_cast<double>(memory::get_allocation_size())/static_cast<double>(1024*1024);
        verbose_stream() 
            << "(" << m_id
            << " :num-exprs " << m_stack.num_exprs()
            << " :time " << std::fixed << std::setprecision(2) << m_watch.get_seconds()
            << " :before-memory " << std::fixed << std::setprecision(2) << m_start_memory
            << " :after-memory " << std::fixed << std::setprecision(2) << end_memory
            << ")" << std::endl;
    }
};

stream_report::stream_report(char const * id, assertion_stream & s) {
    if (get_verbosity_level() >= TACTIC_VERBOSITY_LVL)
        m_imp = alloc(imp, id, s);
    else
        m_imp = 0;
}

stream_report::~stream_report() {
    if (m_imp)
        dealloc(m_imp);
}

