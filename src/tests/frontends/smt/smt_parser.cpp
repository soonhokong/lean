/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include "builtin.h"
#include "smt_parser.h"
#include "smt_pp.h"
#include "printer.h"
#include "exception.h"
#include "test.h"
using namespace lean;
using namespace smt;

static void parse(frontend & fe, char const * str) {
    frontend child = fe.mk_child();
    std::istringstream in(str);
    if (parse_commands(child, in)) {
        formatter fmt = mk_pp_formatter(child);
        std::for_each(child.begin_local_objects(),
                      child.end_local_objects(),
                      [&](object const & obj) {
                          std::cout << fmt(obj) << "\n";
                          std::cout << obj << "\n";
                      });
    }
}

// static void tst1() {
//     frontend fe;
//     parse(fe, "Variable x : Bool Variable y : Bool Axiom H : x && y || x => x");
//     parse(fe, "Eval true && true");
//     parse(fe, "Show true && false Eval true && false");
//     parse(fe, "Infixl 35 & : and Show true & false & false Eval true & false");
//     parse(fe, "Notation 100 if _ then _ fi : implies Show if true then false fi");
//     parse(fe, "Show Pi (A : Type), A -> A");
//     parse(fe, "Check Pi (A : Type), A -> A");
// }

static void check(frontend const & fe, char const * str, expr const & expected) {
    std::cout << "Check: " << str << std::endl;
    std::cout << "==================================" << std::endl;
    std::istringstream in(str);
    try {
        expr got = parse_term(fe, in);
        lean_assert(expected == got);
    } catch (exception &) {
        lean_unreachable();
    }
    std::cout << "==================================" << std::endl;
}

static void tst2() {
    frontend fe;
    fe.add_var("x", Bool);
    fe.add_var("y", Bool);
    fe.add_var("z", Bool);
    expr x = Const("x"); expr y = Const("y"); expr z = Const("z");
    check(fe, "(and x y)", And(x, y));
    check(fe, "(or (and x y) z)", Or(And(x, y), z));
    check(fe, "(or (x (and y z))", Or(x, And(y, z)));
    check(fe, "(or x (or y (and x z)))", Or(x, Or(y, And(x, z))));
    check(fe, "(=> (or x y (and x z)) (and x y))", Implies(Or(x, Or(y, And(x, z))), And(x, y)));
    check(fe, "(implies (x (implies y (implies z x))))", Implies(x, Implies(y, Implies(z, x))));
    check(fe, "(implies x (implies (implies y z) x))", Implies(x, Implies(Implies(y, z), x)));
}

int main() {
    // tst1();
    tst2();
    return has_violations() ? 1 : 0;
}
