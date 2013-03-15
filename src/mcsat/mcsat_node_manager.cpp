/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_node_manager.cpp

Abstract:

    Object for creating new nodes and 
    maintaining the mapping between nodes
    and expressions.

Author:

    Leonardo de Moura (leonardo) 2012-12-19

Revision History:

*/
#include"mcsat_node_manager.h"
#include"obj_hashtable.h"

namespace mcsat {

    node_manager::node_manager() {
    }

    node_manager::~node_manager() {
    }

    void node_manager::push() {
        m_scopes.push_back(m_node2expr.size());
    }

    void node_manager::pop(unsigned num_scopes) {
        SASSERT(num_scopes <= m_scopes.size());
        unsigned new_lvl    = m_scopes.size() - num_scopes;
        unsigned old_sz     = m_scopes[new_lvl];
        SASSERT(old_sz <= m_node2expr.size());
        for (unsigned i = old_sz; i < m_node2expr.size(); i++) {
            m_expr2node.erase(m_node2expr[i]);
        }
        m_node2expr.shrink(old_sz);
        m_node2lvl.shrink(old_sz);
        m_internalized.shrink(old_sz);
        m_scopes.shrink(new_lvl);
    }

    node node_manager::mk_node(expr * n) {
        node r(m_node2expr.size());
        obj_map<expr, node>::key_data const & kd = m_expr2node.insert_if_not_there(n, r);
        if (kd.m_value.index() != r.index())
            return kd.m_value; // node already exists.
        m_node2expr.push_back(n);
        m_node2lvl.push_back(m_scopes.size());
        m_internalized.push_back(false);
        return r;
    }

    bool node_manager::contains(expr * n) const {
        return m_expr2node.contains(n);
    }
    
};
