/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_default_solver.h

Abstract:

    MCSAT solver pre-configured with several tactics 
    and components.

Author:

    Leonardo de Moura (leonardo) 2012-12-13.

Revision History:

--*/
#ifndef _MCSAT_DEFAULT_SOLVER_H_
#define _MCSAT_DEFAULT_SOLVER_H_

#include"mcsat_solver.h"

namespace mcsat {
    
    class default_solver_factory : public solver_factory {
    public:
        default_solver_factory();
        virtual ~default_solver_factory();
    };
    
};

#endif
