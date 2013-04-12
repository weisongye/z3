/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    pull_nested_quantifiers_tactic.cpp

Abstract:

    Pull nested quantifiers.

Author:

    Leonardo (leonardo) 2013-04-11

Notes:

--*/
#include"tactical.h"
#include"pull_quant.h"
#include"assertion_stream.h"

class pull_nested_quantifiers_tactic : public tactic {

    void apply(assertion_stream & g) {
        ast_manager & m = g.m();
        pull_nested_quant proc(m);
        if (g.inconsistent())
            return;
        stream_report report("pull-nested-quantifiers", g);
        SASSERT(g.is_well_sorted());
        expr_ref   new_curr(m);
        proof_ref  new_pr(m);
        unsigned size = g.size();
        for (unsigned idx = g.qhead(); idx < size; idx++) {
            if (g.inconsistent())
                break;
            expr * curr = g.form(idx);
            proc(curr, new_curr, new_pr);
            if (g.proofs_enabled()) {
                proof * pr = g.pr(idx);
                new_pr     = m.mk_modus_ponens(pr, new_pr);
            }
            g.update(idx, new_curr, new_pr, g.dep(idx));
        }
        g.inc_depth();
        SASSERT(g.is_well_sorted());
    }

public:
    pull_nested_quantifiers_tactic() {}
    virtual ~pull_nested_quantifiers_tactic() {}

    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        mc = 0; pc = 0; core = 0;
        goal2stream s(*(g.get()));
        apply(s);
        result.push_back(g.get());
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(pull_nested_quantifiers_tactic);
    }

    virtual void operator()(assertion_stack & s) {
        assertion_stack2stream strm(s);
        apply(strm);
    }

    virtual void cleanup() {}
};

tactic * mk_pull_nested_quantifiers_tactic(ast_manager & m, params_ref const & p) {
    return alloc(pull_nested_quantifiers_tactic);
}

