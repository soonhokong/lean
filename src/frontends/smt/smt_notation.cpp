/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
        Soonho Kong
*/
#include "builtin.h"
#include "smt_frontend.h"

namespace lean {
namespace smt {
/**
   \brief Initialize builtin notation.
*/
void init_builtin_notation(frontend & f) {
    f.add_prefix("not", 40, mk_not_fn());
    f.add_infixr("and", 35, mk_and_fn());
    f.add_infixr("or", 30, mk_or_fn());
    f.add_infixr("=>", 25, mk_implies_fn());
}
}
}
