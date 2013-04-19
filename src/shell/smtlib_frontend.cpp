/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smtlib_frontend.cpp

Abstract:

    Frontend for reading Smtlib input files

Author:

    Nikolaj Bjorner (nbjorner) 2006-11-3.

Revision History:

    Leonardo de Moura: new SMT 2.0 front-end, removed support for .smtc files and smtcmd_solver object.

--*/
#include<iostream>
#include<time.h>
#include<signal.h>
#include"smtlib_solver.h"
#include"timeout.h"
#include"smt2parser.h"
#include"dl_cmds.h"
#include"dbg_cmds.h"
#include"polynomial_cmds.h"
#include"subpaving_cmds.h"
#include"smt_strategic_solver.h"

extern bool g_display_statistics;
extern void display_config();
static clock_t             g_start_time;
static smtlib::solver*     g_solver      = 0;
static cmd_context *       g_cmd_context = 0;

static void display_statistics() {
    clock_t end_time = clock();
    if ((g_solver || g_cmd_context) && g_display_statistics) {
        std::cout.flush();
        std::cerr.flush();
        if (g_solver) {
            g_solver->display_statistics();
            memory::display_max_usage(std::cout);
            std::cout << "time:               " << ((static_cast<double>(end_time) - static_cast<double>(g_start_time)) / CLOCKS_PER_SEC) << " secs\n";
        }
        else if (g_cmd_context) {
            g_cmd_context->set_regular_stream("stdout");
            g_cmd_context->display_statistics(true, ((static_cast<double>(end_time) - static_cast<double>(g_start_time)) / CLOCKS_PER_SEC));
        }
    }
}

static void on_timeout() {
    display_statistics();
    exit(0);
}

static void on_ctrl_c(int) {
    signal (SIGINT, SIG_DFL);
    display_statistics();
    raise(SIGINT);
}

unsigned read_smtlib_file(char const * benchmark_file) {
    g_start_time = clock();
    register_on_timeout_proc(on_timeout);
    signal(SIGINT, on_ctrl_c);
    smtlib::solver solver;
    g_solver = &solver;
    
    bool ok = true;
    
    ok = solver.solve_smt(benchmark_file);
    if (!ok) {
        if (benchmark_file) {
            std::cerr << "ERROR: solving '" << benchmark_file << "'.\n";
        }
        else {
            std::cerr << "ERROR: solving input stream.\n";
        }
    }
    
    display_statistics();
    register_on_timeout_proc(0);
    g_solver = 0;
    return solver.get_error_code();
}

#include"pre_solver_adapter.h"
#include"smt_solver.h"
#include"simplify_tactic.h"
#include"miniscope_tactic.h"
#include"der_tactic.h"
#include"propagate_values_tactic.h"
#include"expand_macros_tactic.h"
#include"elim_patterns_tactic.h"
#include"solve_eqs_tactic.h"
#include"nnf_tactic.h"
#include"elim_array_tactic.h"
#include"pull_nested_quantifiers_tactic.h"
#include"qsolver_adapter.h"

// Temporary hack to test solver infrastructure
// TODO: implement set-solver command
struct my_solver_factory : public solver_factory {
    virtual ~my_solver_factory() {}
    virtual solver * operator()(ast_manager & m, params_ref const & p, bool proofs_enabled, bool models_enabled, bool unsat_core_enabled, symbol const & logic) {
        solver * gkernel  = mk_smt_solver(m, p, logic);
        solver * kernel   = mk_qsolver_adapter(m, gkernel, p, proofs_enabled, models_enabled, unsat_core_enabled);
        pre_solver_adapter * s = alloc(pre_solver_adapter, m, kernel, p, proofs_enabled, models_enabled, unsat_core_enabled);
        params_ref nnf_p;
        nnf_p.set_bool("ignore_labels", true);
        s->add_tactic_after(mk_elim_patterns_tactic(m));
        s->add_tactic_after(mk_simplify_tactic(m));
        s->add_tactic_after(mk_propagate_values_tactic(m));
        s->add_tactic_after(mk_miniscope_tactic(m));
        s->add_tactic_after(mk_snf_tactic(m, nnf_p));
        s->add_tactic_after(mk_elim_array_tactic(m));
        s->add_tactic_after(mk_der_tactic(m));
       // s->add_tactic_after(mk_expand_macros_tactic(m));
        s->add_tactic_after(mk_der_tactic(m));
        s->add_tactic_after(mk_simplify_tactic(m));
        s->add_tactic_after(mk_pull_nested_quantifiers_tactic(m));
        s->add_tactic_after(mk_solve_eqs_tactic(m));
        params_ref simp_p;
        //simp_p.set_bool("arith_lhs", true);
        s->add_tactic_after(mk_simplify_tactic(m, simp_p));
        return s;
    }
};

solver_factory * get_my_solver_factor() {
    return alloc(my_solver_factory);
}

unsigned read_smtlib2_commands(char const * file_name) {
    g_start_time = clock();
    register_on_timeout_proc(on_timeout);
    signal(SIGINT, on_ctrl_c);
    cmd_context ctx;

    // ctx.set_solver_factory(mk_smt_strategic_solver_factory());
    ctx.set_solver_factory(get_my_solver_factor());
    
    install_dl_cmds(ctx);
    install_dbg_cmds(ctx);
    install_polynomial_cmds(ctx);
    install_subpaving_cmds(ctx);

    g_cmd_context = &ctx;
    register_on_timeout_proc(on_timeout);
    signal(SIGINT, on_ctrl_c);
    
    bool result = true;
    if (file_name) {
        std::ifstream in(file_name);
        if (in.bad() || in.fail()) {
            std::cerr << "(error \"failed to open file '" << file_name << "'\")" << std::endl;
            exit(ERR_OPEN_FILE);
        }
        result = parse_smt2_commands(ctx, in);
    }
    else {
        result = parse_smt2_commands(ctx, std::cin, true);
    }
    
    display_statistics();
    g_cmd_context = 0;
    return result ? 0 : 1;
}

