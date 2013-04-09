/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    solver.h

Abstract:

    abstract solver interface

Author:

    Leonardo (leonardo) 2011-03-19

Notes:

--*/
#include"solver.h"
#include"solver_exception.h"

solver::~solver() {
}

void solver::updt_params(params_ref const & p) {
}

void solver::collect_param_descrs(param_descrs & r) {
}

void solver::set_produce_models(bool f) {
}

void solver::set_cancel(bool f) {
}

unsigned solver::get_scope_level() const {
    throw solver_exception("solver does not support get_scope_level");
    return 0;
}

unsigned solver::get_num_assertions() const {
    throw solver_exception("solver does not support get_num_assertions");
    return 0;
}

expr * solver::get_assertion(unsigned idx) const {
    throw solver_exception("solver does not support get_assertion");
    return 0;
}

void solver::display(std::ostream & out) const {
    out << "(solver)";
}

