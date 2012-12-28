/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_preprocessor.h

Abstract:

    MCSAT preprocessor

Author:

    Leonardo de Moura (leonardo) 2012-11-01.

Revision History:

--*/
#ifndef _MCSAT_PREPROCESSOR_H_
#define _MCSAT_PREPROCESSOR_H_

#include"ast.h"
#include"model.h"

class tactic;

namespace mcsat {

    /**
       \brief MCSAT preprocessor can be customized with tactics that
       can process assertion_stacks.
    */
    class preprocessor {
        struct imp;
        imp * m_imp;
    public:
        preprocessor(ast_manager & m, bool proofs_enabled, bool models_enabled, bool core_enabled);
        ~preprocessor();
        
        ast_manager & m() const;

        bool models_enabled() const;
        bool proofs_enabled() const;
        bool unsat_core_enabled() const;
        
        /**
           \brief Add a tactic to be applied before the existing ones.
        */
        void add_tactic_before(tactic * t);
        /**
           \brief Add a tactic to be applied after the existing ones.
        */
        void add_tactic_after(tactic * t);

        void assert_expr(expr * f, proof * pr, expr_dependency * d);
        void assert_expr(expr * f);
        
        void commit();
        void push();
        void pop(unsigned num_scopes);
        unsigned scope_lvl() const;

        void set_cancel(bool f);
     
        unsigned qhead() const;
        unsigned size() const;
        expr * form(unsigned i) const;
        proof * pr(unsigned i) const;
        expr_dependency * dep(unsigned i) const;
        
        bool inconsistent() const;

        bool is_well_sorted() const;
        
        void convert(model_ref & m);
        
        void freeze(func_decl * f);
        bool is_frozen(func_decl * f) const;
        bool is_eliminated(app * x) const;

        void display(std::ostream & out) const;
    };

};

#endif 
