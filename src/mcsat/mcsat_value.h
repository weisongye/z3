/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_value.h

Abstract:

    Abstract values that are used as values for non-Boolean nodes.
    The mcsat trail has assignments of the form: node -> value

Author:

    Leonardo de Moura (leonardo) 2012-12-17

Revision History:

*/
#ifndef _MCSAT_VALUE_H_
#define _MCSAT_VALUE_H_

namespace mcsat {
    
    class value {
        unsigned m_val;
        explicit value(unsigned id):m_val(id) { SASSERT(id < UINT_MAX); }
        friend class value_manager;
    public:
        value():m_val(UINT_MAX) {}
        unsigned index() const { return m_val; }
        unsigned hash() const { return m_val; }
        friend bool operator==(value const & n1, value const & n2) { return n1.m_val == n2.m_val; }
        friend bool operator!=(value const & n1, value const & n2) { return n1.m_val != n2.m_val; }
        friend bool operator<(value const & n1, value const & n2)  { return n1.m_val < n2.m_val; }
    };
    
    const value null_value;
};

#endif
