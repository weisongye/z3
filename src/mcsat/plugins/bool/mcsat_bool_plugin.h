/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_bool_plugin.h

Abstract:

    Standard plugin for propositional logic.
    
Author:

    Leonardo de Moura (leonardo) 2012-12-22

Revision History:

*/
#ifndef _MCSAT_BOOL_PLUGIN_H_
#define _MCSAT_BOOL_PLUGIN_H_

namespace mcsat {
    class plugin;
    plugin * mk_bool_plugin();
};

#endif
