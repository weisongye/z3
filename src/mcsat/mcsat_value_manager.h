/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_value_manager.h

Abstract:

    Object for maintaining the set of values being used in mcsat.

Author:

    Leonardo de Moura (leonardo) 2012-12-19

Revision History:

*/
#ifndef _MCSAT_VALUE_MANAGER_H_
#define _MCSAT_VALUE_MANAGER_H_

#include"ast.h"
#include"mcsat_value.h"

namespace mcsat {

    class value_manager {
        unsigned         m_next_id;
        unsigned_vector  m_scopes;

        friend class kernel;
        value_manager();
        ~value_manager();
        void push();
        void pop(unsigned num_scopes);
    public:
        value mk_value();
        unsigned size() const { return m_next_id; }
    };

};

#endif
