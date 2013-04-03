/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_solver.cpp

Abstract:

    mcsat solver

Author:

    Leonardo de Moura (leonardo) 2012-11-01.

Revision History:

--*/
#include"mcsat_solver.h"
#include"mcsat_kernel.h"

namespace mcsat {

    solver_factory::~solver_factory() {
    }

    void solver_factory::add_plugin(plugin * p) {
        m_plugins.push_back(p);
    }

    pre_solver_adapter * solver_factory::mk_solver(ast_manager & m, params_ref const & p, bool proofs_enabled, bool models_enabled, bool unsat_core_enabled, symbol const & logic) {
        kernel * k = alloc(kernel, m, proofs_enabled);
        unsigned sz = m_plugins.size();
        for (unsigned i = 0; i < sz; i++) {
            k->add_plugin(m_plugins.get(i));
        }
        return alloc(pre_solver_adapter, m, k, p, proofs_enabled, models_enabled, unsat_core_enabled);
    }

};
