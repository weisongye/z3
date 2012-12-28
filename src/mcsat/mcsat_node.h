/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_node.h

Abstract:

      Nodes are the elements that are assigned in the mcsat trail.

Author:

    Leonardo de Moura (leonardo) 2012-12-17

Revision History:

*/
#ifndef _MCSAT_NODE_H_
#define _MCSAT_NODE_H_

#include<limits.h>
#include"debug.h"

namespace mcsat {
    
    class node {
        unsigned m_val;
        explicit node(unsigned id):m_val(id) { SASSERT(id <= (UINT_MAX >> 1)); }
        friend class node_manager;
        friend class literal;
    public:
        node():m_val(UINT_MAX >> 1) {}
        unsigned index() const { return m_val; }
        unsigned hash() const { return m_val; }
        friend bool operator==(node const & n1, node const & n2) { return n1.m_val == n2.m_val; }
        friend bool operator!=(node const & n1, node const & n2) { return n1.m_val != n2.m_val; }
        friend bool operator<(node const & n1, node const & n2)  { return n1.m_val < n2.m_val; }
    };
    
    const node null_node;

};

#endif
