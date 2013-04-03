/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_solver.h

Abstract:

    mcsat solver

Author:

    Leonardo de Moura (leonardo) 2012-11-01.

Revision History:

--*/
#include"mcsat_plugin.h"
#include"pre_solver_adapter.h"

namespace mcsat {

    typedef pre_solver_adapter solver;

    class solver_factory : public pre_solver_adapter_factory {    
        plugin_ref_vector   m_plugins;
    protected:
        virtual pre_solver_adapter * mk_solver(ast_manager & m, params_ref const & p, bool proofs_enabled, bool models_enabled, bool unsat_core_enabled, symbol const & logic);
    public:
        virtual ~solver_factory();
        void add_plugin(plugin * p);
    };
};
