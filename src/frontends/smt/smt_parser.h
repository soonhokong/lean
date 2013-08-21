/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include "smt_frontend.h"

namespace lean {
namespace smt {
bool parse_commands(frontend & fe, std::istream & in, bool use_exceptions = true);
bool parse_commands_from_stdin(frontend & fe);
// expr parse_expr(frontend const & fe, std::istream & in);
}
}
