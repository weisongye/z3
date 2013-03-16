/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_node_manager.h

Abstract:

    Object for creating new nodes and 
    maintaining the mapping between nodes
    and expressions.

Author:

    Leonardo de Moura (leonardo) 2012-12-19

Revision History:

*/
#ifndef _MCSAT_NODE_MANAGER_H_
#define _MCSAT_NODE_MANAGER_H_

#include"ast.h"
#include"mcsat_node.h"

namespace mcsat {

    /**
       \brief Node manager is the object used to create nodes and
       manage the mapping between nodes and expressions.
    */
    class node_manager {
        obj_map<expr, node> m_expr2node;
        ptr_vector<expr>    m_node2expr;
        unsigned_vector     m_node2lvl;
        unsigned_vector     m_scopes;

        friend class kernel;
        node_manager();
        ~node_manager();
        void push();
        void pop(unsigned num_scopes);
        /**
           \brief Return the level where the given node was created.
        */
        unsigned get_mk_level(node n) { return m_node2lvl[n.index()]; }
    public:
        /**
           \brief Create a new node for the expression if it does not exist yet.
           
           Only expressions that are in the preprocessor stack or stored in the
           expr_manager can be save in the node_manager.
        */
        node mk_node(expr * n);
        /**
           \brief Return true if the expression already has a node associated with it.
        */
        bool contains(expr * n) const;
        /**
           \brief Return the number of nodes in this manager.
        */
        unsigned size() const { return m_node2expr.size(); }
        /**
           \brief Return the expression associated with the given node.
        */
        expr * to_expr(node n) const { return m_node2expr[n.index()]; }
    };
    
};

#endif
