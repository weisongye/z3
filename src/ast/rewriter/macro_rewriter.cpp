/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    macro_rewriter.cpp

Abstract:

    Goodies for rewriting macros

Author:

    Leonardo (leonardo) 2013-02-11

Notes:

--*/
#include"macro_rewriter.h"
#include"var_subst.h"

void normalize_macro(ast_manager & m, app * head, expr * def, expr_ref & new_def) {
    // check if the transformation is needed
    unsigned num_args = head->get_num_args();
    unsigned i;
    for (i = 0; i < num_args; i++) {
        var * x = to_var(head->get_arg(i));
        if (x->get_idx() != i)
            break;
    }
    if (i == num_args) {
        new_def = def;
        return;
    }
    expr_ref_buffer  var_mapping(m);
    unsigned max      = num_args;
    for (unsigned i = 0; i < num_args; i++) {
        var * x     = to_var(head->get_arg(i));
        if (x->get_idx() >= max)
            max = x->get_idx() + 1;
    }
    for (unsigned i = 0; i < num_args; i++) {
        var * x     = to_var(head->get_arg(i));
        if (x->get_idx() != i) {
            var * new_x = m.mk_var(i, x->get_sort());
            SASSERT(x->get_idx() < max);
            var_mapping.setx(max - x->get_idx() - 1, new_x);
        }
        else {
            var_mapping.setx(max - i - 1, x);
        }
    }
    // REMARK: t may have nested quantifiers... So, I must use the std order for variable substitution.
    var_subst subst(m);
    subst(def, var_mapping.size(), var_mapping.c_ptr(), new_def);
}
