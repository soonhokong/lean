/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
        Leonardo de Moura
*/
#pragma once
#include <iostream>
#include "smt_frontend.h"
#include "interruptable_ptr.h"

namespace lean {
namespace smt {

class parser {
    class imp;
    std::unique_ptr<imp> m_ptr;
public:
    parser(frontend fe, std::istream & in, bool use_exceptions = true, bool interactive = false);
    ~parser();

    /** \brief Parse a sequence of commands */
    bool operator()();

    /** \brief Parse a single term */
    expr parse_term();

    void set_interrupt(bool flag);
    void interrupt() { set_interrupt(true); }
    void reset_interrupt() { set_interrupt(false); }
};

/** \brief Implements the Read Eval Print loop */
class shell {
    frontend                  m_frontend;
    interruptable_ptr<parser> m_parser;
public:
    shell(frontend & fe);
    ~shell();

    bool operator()();

    void set_interrupt(bool flag);
    void interrupt() { set_interrupt(true); }
    void reset_interrupt() { set_interrupt(false); }
};

inline bool parse_commands(frontend & fe, std::istream & in, bool use_exceptions = true, bool interactive = false) {
    return parser(fe, in, use_exceptions, interactive)();
}
inline expr parse_term(frontend const & fe, std::istream & in) {
    return parser(fe, in).parse_term();
}
}
}
