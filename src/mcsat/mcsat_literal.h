/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_literal.h

Abstract:

    A literal is a pair (node, sign), where node is Boolean.

Author:

    Leonardo de Moura (leonardo) 2012-12-17

Revision History:

*/
#ifndef _MCSAT_LITERAL_H_
#define _MCSAT_LITERAL_H_

#include"mcsat_node.h"
#include"vector.h"

namespace mcsat {

    class literal {
        unsigned m_val;
        explicit literal(unsigned v):m_val(v) {}
    public:
        literal():m_val(null_node.index() << 1) { SASSERT(var() == null_node && !sign()); }
        literal(node n, bool _sign):
            m_val((n.index() << 1) + static_cast<unsigned>(_sign)) {
            SASSERT(var() == n);
            SASSERT(sign() == _sign);
        }
        node var() const { return node(m_val >> 1); }
        bool sign() const { return m_val & 1; }
        literal unsign() const { return literal(m_val & ~1); }
        unsigned index() const { return m_val; }
        void neg() { m_val = m_val ^ 1; }
        unsigned hash() const { return index(); }
        friend literal operator~(literal l) { return literal(l.m_val ^ 1); }
        friend bool operator<(literal const & l1, literal const & l2) { return l1.m_val < l2.m_val; }
        friend bool operator==(literal const & l1, literal const & l2) { return l1.m_val == l2.m_val; }
        friend bool operator!=(literal const & l1, literal const & l2) { return l1.m_val != l2.m_val; }
    };

    const literal null_literal;
    typedef svector<literal> literal_vector;
    
};

#endif
