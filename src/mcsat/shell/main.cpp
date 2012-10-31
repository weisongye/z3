/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat minimalistic front-end.

Abstract:

    mcsat command line tool.

Author:

    Leonardo de Moura (leonardo) 2012-10-31.

Revision History:

--*/
#include<iostream>
#include<time.h>
#include<signal.h>
#include"version.h"
#include"timeout.h"
#include"cmd_context.h"
#include"smt2parser.h"

char const *         g_input_file          = 0;
bool                 g_display_statistics  = false;
static clock_t       g_start_time;
static cmd_context * g_cmd_context = 0;

#define MCSAT "mcs"

void error(const char * msg) {
    std::cerr << "Error: " << msg << "\n";
    std::cerr << "For usage information: " << MCSAT << " -h\n";
    exit(ERR_CMD_LINE);
}

void display_usage() {
    std::cout << MCSAT << " [version " << Z3_MAJOR_VERSION << "." << Z3_MINOR_VERSION << "." << Z3_BUILD_NUMBER << " - ";
#ifdef _AMD64_
    std::cout << "64";
#else
    std::cout << "32";
#endif
    std::cout << " bit]. (C) Copyright 2012 Microsoft Corp.\n";
    std::cout << "Usage: " << MCSAT << " [options] file.smt2\n";
    std::cout << "\nMiscellaneous:\n";
    std::cout << "  -h, -?      prints this message.\n";
    std::cout << "  -version    prints version number of mcsat.\n";
    std::cout << "  -v:level    be verbose, where <level> is the verbosity level.\n";
    std::cout << "  -nw         disable warning messages.\n";
    std::cout << "  -st         display statistics.\n";
    std::cout << "  -t:secs     set timeout.\n";
#if defined(Z3DEBUG) || defined(_TRACE)
    std::cout << "\nDebugging support:\n";
#endif
#ifdef _TRACE
    std::cout << "  -tr:tag     enable trace messages tagged with <tag>.\n";
#endif
#ifdef Z3DEBUG
    std::cout << "  -dbg:tag    enable assertions tagged with <tag>.\n";
#endif
}

void parse_cmd_line_args(int argc, char ** argv) {
    int i = 1;
    while (i < argc) {
        char * arg = argv[i];    

        if (arg[0] == '-') {
            char * opt_name = arg + 1;
            char * opt_arg  = 0;
            char * colon    = strchr(arg, ':');
            if (colon) {
                opt_arg = colon + 1;
                *colon  = 0;
            }
            if (strcmp(opt_name, "h") == 0 || strcmp(opt_name, "?") == 0 || strcmp(opt_name, "help") == 0) {
                display_usage();
                exit(0);
            }
            if (strcmp(opt_name, "version") == 0) {
                std::cout
                    << Z3_MAJOR_VERSION << " " 
                    << Z3_MINOR_VERSION << " "
                    << Z3_BUILD_NUMBER << "\n";
                exit(0);
            }
            else if (strcmp(opt_name, "st") == 0) {
                g_display_statistics = true; 
            }
            else if (strcmp(opt_name, "v") == 0) {
                if (!opt_arg)
                    error("option argument (-v:level) is missing.");
                long lvl = strtol(opt_arg, 0, 10);
                set_verbosity_level(lvl);
            }
            else if (strcmp(opt_name, "t") == 0) {
                if (!opt_arg)
                    error("option argument (-t:timeout) is missing.");
                long tm = strtol(opt_arg, 0, 10);
                set_timeout(tm * 1000);
            }
#ifdef _TRACE
            else if (strcmp(opt_name, "tr") == 0) {
                if (!opt_arg)
                    error("option argument (-tr:tag) is missing.");
                enable_trace(opt_arg);
            }
#endif
#ifdef Z3DEBUG
            else if (strcmp(opt_name, "dbg") == 0) {
                if (!opt_arg)
                    error("option argument (-dbg:tag) is missing.");
                enable_debug(opt_arg);
            }
#endif
            else {
                std::cerr << "Error: invalid command line option: " << arg << "\n";
                std::cerr << "For usage information: " << MCSAT << " -h\n";
                exit(ERR_CMD_LINE);
            }
        }
        else {
            if (g_input_file) {
                warning_msg("input file was already specified.");
            }
            else {
                g_input_file = arg;
            }
        }
        i++;
    }
}

static void display_statistics() {
    clock_t end_time = clock();
    if (g_cmd_context && g_display_statistics) {
        std::cout.flush();
        std::cerr.flush();
        g_cmd_context->set_regular_stream("stdout");
        g_cmd_context->display_statistics(true, ((static_cast<double>(end_time) - static_cast<double>(g_start_time)) / CLOCKS_PER_SEC));
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

unsigned read_smtlib2_commands(char const * file_name) {
    g_start_time = clock();
    register_on_timeout_proc(on_timeout);
    signal(SIGINT, on_ctrl_c);
    cmd_context ctx;

    // solver * s = mk_smt_strategic_solver(ctx);
    // ctx.set_solver(s);

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

int main(int argc, char ** argv) {
    try {
        memory::initialize(0);
        parse_cmd_line_args(argc, argv);
        if (!g_input_file) {
            error("input file was not specified.");
        }
        memory::exit_when_out_of_memory(true, "(error \"out of memory\")");
        return read_smtlib2_commands(g_input_file);
    }
    catch (z3_exception & ex) {
        // unhandled exception
        std::cerr << "ERROR: " << ex.msg() << "\n";
        if (ex.has_error_code())
            return ex.error_code();
        else
            return ERR_INTERNAL_FATAL;
    }
}




