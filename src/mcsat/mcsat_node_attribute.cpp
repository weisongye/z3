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
#include"mcsat_node_attribute.h"
#include"mcsat_node_manager.h"

namespace mcsat {

    template<typename T>
    void node_attribute<T>::save(ptr_vector<expr> const & to_save) {
        SASSERT(m_saved_values.empty());
        for (unsigned i = 0; i < to_save.size(); i++) {
            expr * t = to_save[i];
            node n   = m_manager.mk_node(t);
            if (contains(n))
                m_saved_values.push_back(expr_attr(t, m_values[n.index()]));
        }
    }

    template<typename T>
    void node_attribute<T>::restore() {
        for (unsigned i = 0; i < m_saved_values.size(); i++) {
            expr * t = m_saved_values[i].first;
            if (m_manager.contains(t)) {
                node n = m_manager.mk_node(t);
                set(n, m_saved_values[i].second);
            }
        }
        m_saved_values.reset();
        m_values.shrink(m_manager.size());
        m_contains.shrink(m_manager.size());
    }
    
    template<typename T>
    node_attribute<T>::node_attribute(node_manager & m):m_manager(m) {
    }

    template<typename T>
    node_attribute<T>::~node_attribute() {
    }

    template<typename T>
    bool node_attribute<T>::contains(node const & n) const {
        unsigned idx = n.index();
        return idx < m_contains.size() && m_contains[idx] != 0;
    }
    
    template<typename T>
    T const & node_attribute<T>::get_value(node const & n, T const & def) const {
        if (!contains(n))
            return def;
        return m_values[n.index()];
    }
    
    template<typename T>
    void node_attribute<T>::set(node const & n, T const & v) {
        unsigned idx = n.index();
        if (idx >= m_values.size()) {
            m_contains.resize(idx+1, 0);
            m_values.resize(idx+1, v); // the value doesn't really matter
        }
        m_contains[idx] = 1;
        m_values[idx]   = v;
    }

    node_attribute_manager::node_attribute_manager(node_manager & m):
        m_manager(m) {
    }

    node_attribute_manager::~node_attribute_manager() {
    }

    void node_attribute_manager::save(ptr_vector<expr> const & to_save) {
        for (unsigned i = 0; i < m_attributes.size(); i++)
            m_attributes[i]->save(to_save);
    }
    
    void node_attribute_manager::restore() {
        for (unsigned i = 0; i < m_attributes.size(); i++)
            m_attributes[i]->restore();
    }
    
    template<typename T>
    node_attribute<T> & node_attribute_manager::mk_attribute() {
        node_attribute<T> * r = alloc(node_attribute<T>, m_manager);
        m_attributes.push_back(r);
        return *r;
    }

    node_uint_attribute & node_attribute_manager::mk_uint_attribute() { 
        return mk_attribute<unsigned>(); 
    }
    
    node_double_attribute & node_attribute_manager::mk_double_attribute() { 
        return mk_attribute<double>(); 
    }

    template class node_attribute<unsigned>;
    template class node_attribute<double>;
};
