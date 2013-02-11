/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    macro_rewriter.h

Abstract:

    Goodies for rewriting macros

Author:

    Leonardo (leonardo) 2013-02-11

Notes:

--*/
#ifndef _MACRO_REWRITER_H_
#define _MACRO_REWRITER_H_

#include"ast.h"

/**
   \brief Normalize definition of the form head = f(x0, x1, ..., xn) == def[x0, ..., xn].
   It makes sure the first argument is variable 0, the second variable 1, and so on.

   The variables in head may be in the wrong order.
   Example: f(x_1, x_0) instead of f(x_0, x_1)
   This method is essentially renaming the variables in def.
   Suppose def is g(x_1, x_0 + x_1)
   This method will store g(x_0, x_1 + x_0) in new_def.

   f(x_1, x_2) --> f(x_0, x_1)
   f(x_3, x_2) --> f(x_0, x_1)
*/
void normalize_macro(ast_manager & m, app * head, expr * def, expr_ref & new_def);

#endif
