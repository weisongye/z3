/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_value_manager.cpp

Abstract:

    Object for maintaining the set of values being used in mcsat.

Author:

    Leonardo de Moura (leonardo) 2012-12-19

Revision History:

*/
#include"mcsat_value_manager.h"

namespace mcsat {
    
    value_manager::value_manager() {
        m_next_id = 0;
    }
    
    value_manager::~value_manager() {
    }

    void value_manager::push() {
        m_scopes.push_back(m_next_id);
    }

    void value_manager::pop(unsigned num_scopes) {
        SASSERT(num_scopes <= m_scopes.size());
        unsigned new_lvl    = m_scopes.size() - num_scopes;
        m_next_id           = m_scopes[new_lvl];
        m_scopes.shrink(new_lvl);
    }

    value value_manager::mk_value() { 
        value r(m_next_id);
        m_next_id++;
        return r;
    }
    
};
