/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    qsolver_adapter.h

Abstract:

    Add support for quantifiers to a ground solver.

Author:

    Leonardo de Moura (leonardo) 2013-04-09.

Revision History:

--*/
#ifndef _QSOLVER_ADAPTER_H_
#define _QSOLVER_ADAPTER_H_

#include"solver.h"

solver * mk_qsolver_adapter(ast_manager & m, solver * s, params_ref const & p, bool produce_proofs, bool produce_models, bool produce_unsat_cores);

#endif
