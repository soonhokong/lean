/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
        Soonho Kong
*/
#pragma once
#include "util/sexpr/options.h"
#include "kernel/context.h"
#include "library/formatter.h"

namespace lean {
namespace smt {
class frontend;
formatter mk_pp_formatter(frontend const & fe);
std::ostream & operator<<(std::ostream & out, frontend const & fe);
}
}
