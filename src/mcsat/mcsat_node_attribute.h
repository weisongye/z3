/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_node_attribute.h

Abstract:

    Facility for managing attributes that must be persistent
    when a node is deleted and recreated by MCSat during cleanup.

Author:

    Leonardo de Moura (leonardo) 2012-12-19

Revision History:

*/
#ifndef _MCSAT_NODE_ATTRIBUTE_H_
#define _MCSAT_NODE_ATTRIBUTE_H_

#include"ast.h"
#include"scoped_ptr_vector.h"

namespace mcsat {
    class node_manager;
    class node;

    class node_attribute_core {
    protected:
        friend class node_attribute_manager;
        virtual void save(ptr_vector<expr> const & to_save) = 0;
        virtual void restore() = 0;
    public:
        virtual ~node_attribute_core() {}
    };

    template<typename T>
    class node_attribute : public node_attribute_core {
        typedef std::pair<expr *, T> expr_attr;
        node_manager &    m_manager;
        vector<T>         m_values;
        char_vector       m_contains;
        vector<expr_attr> m_saved_values;
        
        friend class node_attribute_manager;
        virtual void save(ptr_vector<expr> const & to_save);
        virtual void restore();
        node_attribute(node_manager & m);
    public:
        virtual ~node_attribute();
        
        bool contains(node const & n) const;
        T & get_value(node const & n, T const & def) const;
        void set(node const & n, T const & v);
    };

    typedef node_attribute<unsigned> node_uint_attribute;
    typedef node_attribute<double>   node_double_attribute;

    class node_attribute_manager {
        node_manager &                         m_manager;
        scoped_ptr_vector<node_attribute_core> m_attributes;

        template<typename T>
        node_attribute<T> & mk_attribute();

        friend class kernel;
        node_attribute_manager(node_manager & m);
        ~node_attribute_manager();
        void save(ptr_vector<expr> const & to_save);
        void restore();
    public:
        node_uint_attribute & mk_uint_attribute() { return mk_attribute<unsigned>(); }
        node_double_attribute & mk_double_attribute() { return mk_attribute<double>(); }
    };

};

#endif
