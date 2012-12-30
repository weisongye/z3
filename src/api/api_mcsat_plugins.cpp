/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_mcsat_plugins.cpp

Abstract:
    MCSat plugins

Author:

    Leonardo de Moura (leonardo) 2012-12-29.

Revision History:

--*/
#include<iostream>
#include"z3.h"
#include"api_log_macros.h"
#include"api_context.h"
#include"api_mcsat_plugins.h"
#include"mcsat_bool_plugin.h"

extern "C" {

    Z3_mcsat_plugin Z3_API Z3_mk_mcsat_plugin(Z3_context c, Z3_string n) {
        Z3_TRY;
        LOG_Z3_mk_mcsat_plugin(c, n);
        RESET_ERROR_CODE();
        std::string name(n);
        mcsat::plugin * p = 0;
        if (name == "Bool")
            p = mcsat::mk_bool_plugin();
        else
            throw default_exception("Unknown MCSat plugin");
        Z3_mcsat_plugin_ref * ref = alloc(Z3_mcsat_plugin_ref);
        ref->m_plugin = p;
        mk_c(c)->save_object(ref);
        Z3_mcsat_plugin result = of_mcsat_plugin(ref);
        RETURN_Z3(result);                              
        Z3_CATCH_RETURN(0);
    }

    void Z3_API Z3_mcsat_plugin_inc_ref(Z3_context c, Z3_mcsat_plugin p) {
        Z3_TRY;
        LOG_Z3_mcsat_plugin_inc_ref(c, p);
        RESET_ERROR_CODE();
        to_mcsat_plugin(p)->inc_ref();
        Z3_CATCH;
    }

    void Z3_API Z3_mcsat_plugin_dec_ref(Z3_context c, Z3_mcsat_plugin p) {
        Z3_TRY;
        LOG_Z3_mcsat_plugin_dec_ref(c, p);
        RESET_ERROR_CODE();
        to_mcsat_plugin(p)->dec_ref();
        Z3_CATCH;
    }

};
