/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_plugin.cpp

Abstract:

    An extension for the mcsat kernel.
    Plugins are used to add:
       - new theory solvers
       - propagators (for pruning the seach space)
       - and any other form of object that can interact with the trail.
Author:

    Leonardo de Moura (leonardo) 2012-12-16

Revision History:

*/
#include"mcsat_plugin.h"

namespace mcsat {

    plugin::~plugin() {
    }

    void plugin::updt_params(params_ref const & p) {
    }

    void plugin::collect_param_descrs(param_descrs & r) {
    }

    void plugin::collect_statistics(statistics & st) const {
    }

    void plugin::set_cancel(bool f) {
    }

    void plugin::display(std::ostream & out) const {
        out << get_name() << std::endl;
    }

    void plugin::init(initialization_context & ctx) {
    }

    bool plugin::internalize(clause * c, clause_internalization_context & ctx) {
        return false;
    }

    void plugin::dettach_clause(clause * c) {
    }

    void plugin::full_propagate(propagation_context & ctx) {
    }

    unsigned plugin::priority() const {
        return 0;
    }

    void plugin::prepare_decision(internalization_context & ctx) {
    }

    decision * plugin::decide(decision_context & ctx) {
        UNREACHABLE();
        return 0;
    }
    
};
