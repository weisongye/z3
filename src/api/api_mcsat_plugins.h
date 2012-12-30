/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_mcsat_plugins.h

Abstract:
    MCSat plugins

Author:

    Leonardo de Moura (leonardo) 2012-12-29.

Revision History:

--*/
#ifndef _API_MCSAT_PLUGINS_H_
#define _API_MCSAT_PLUGINS_H_

#include"mcsat_plugin.h"

struct Z3_mcsat_plugin_ref : public api::object {
    mcsat::plugin_ref m_plugin;
    virtual ~Z3_mcsat_plugin_ref() {}
};

inline Z3_mcsat_plugin_ref * to_mcsat_plugin(Z3_mcsat_plugin p) { return reinterpret_cast<Z3_mcsat_plugin_ref *>(p); }
inline Z3_mcsat_plugin of_mcsat_plugin(Z3_mcsat_plugin_ref * p) { return reinterpret_cast<Z3_mcsat_plugin>(p); }
inline mcsat::plugin * to_mcsat_plugin_ref(Z3_mcsat_plugin p) { return p == 0 ? 0 : to_mcsat_plugin(p)->m_plugin.get(); }

#endif
