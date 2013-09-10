/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include "test.h"
#include "smt_scanner.h"
#include "exception.h"
#include "escaped.h"
using namespace lean;
using namespace smt;

#define st scanner::token

static void scan(char const * str, list<name> const & cmds = list<name>()) {
    std::cout << str << std::endl;
    std::cout << "=> ";
    std::istringstream in(str);
    scanner s(in);
//    for (name const & n : cmds) s.add_command_keyword(n);
    while (true) {
        st t = s.scan();
        if (t == st::Eof)
            break;
        std::cout << t;
        if (t == st::Symbol)
            std::cout << "[" << s.get_name_val() << "]";
        else if (t == st::Keyword)
            std::cout << "[:" << s.get_name_val() << "]";
        else if (t == st::NumVal || t == st::DecVal || t == st::BinVal || t == st::HexVal)
            std::cout << "[" << s.get_num_val() << "]";
        else if (t == st::StringVal)
            std::cout << "[\"" << escaped(s.get_str_val().c_str()) << "\"]";
        std::cout << " ";
    }
    std::cout << std::endl << std::endl;
}

static void check(char const * str, std::initializer_list<scanner::token> const & l, list<name> const & cmds = list<name>()) {
    auto it = l.begin();
    std::istringstream in(str);
    scanner s(in);
//    for (name const & n : cmds) s.add_command_keyword(n);
    while (true) {
        st t = s.scan();
        if (t == st::Eof) {
            lean_assert(it == l.end());
            return;
        }
        lean_assert(it != l.end());
        lean_assert(t == *it);
        ++it;
    }
}

static void check_name(char const * str, name const & expected) {
    std::istringstream in(str);
    scanner s(in);
    st t = s.scan();
    lean_assert(t == st::Symbol);
    lean_assert(s.get_name_val() == expected);
    lean_assert(s.scan() == st::Eof);
}

static void tst1() {
    std::cout << "Basic Boolean Example, SMT-LIBv2 Tutorial " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(set-logic QF_UF)");
    scan("(declare-fun p () Bool)");
    scan("(assert (and p (not p)))");
    scan("(check-sat)");
    scan("(exit)");
    std::cout << "=======================" << std::endl << std::endl;
}

static void tst2() {
    std::cout << "Selecting options, SMT-LIBv2 Tutorial " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(set-option :print-success false)");
    scan("(set-logic QF_UF)");
    scan("(declare-fun p () Bool)");
    scan("(assert (and p (not p)))");
    scan("(check-sat)");
    scan("(exit)");
    std::cout << "=======================" << std::endl << std::endl;
}

static void tst3() {
    std::cout << "Integer Arithmetic - 1, SMT-LIBv2 Tutorial " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(set-logic QF_LIA)");
    scan("(declare-fun x () Int)");
    scan("(declare-fun y () Int)");
    scan("(assert (= (+ x (* 2 y)) 20))");
    scan("(assert (= (- x y) 2))");
    scan("(check-sat)");
    scan("(exit)");
    std::cout << "=======================" << std::endl << std::endl;
}

static void tst4() {
    std::cout << "Integer Arithmetic - 2, SMT-LIBv2 Tutorial " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(set-logic QF_LIA)");
    scan("(declare-fun x () Int)");
    scan("(declare-fun y () Int)");
    scan("(assert (= (+ x (* 2 y)) 20))");
    scan("(assert (= (- x y) 3))");
    scan("(check-sat)");
    scan("(exit)");
    std::cout << "=======================" << std::endl << std::endl;
}

static void tst5() {
    std::cout << "Getting values, SMT-LIBv2 Tutorial " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(set-option :print-success false)");
    scan("(set-option :produce-models true)");
    scan("(set-option :interactive-mode true)");
    scan("(set-logic QF_LIA)");
    scan("(declare-fun x () Int)");
    scan("(declare-fun y () Int)");
    scan("(assert (= (+ x (* 2 y)) 20))");
    scan("(assert (= (- x y) 2))");
    scan("(check-sat)");
    scan("(get-value (x y))");
    scan("(exit)");
    std::cout << "=======================" << std::endl << std::endl;
}

static void tst6() {
    std::cout << "Using scopes to explore multiple problems, SMT-LIBv2 Tutorial " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(set-option :print-success false)");
    scan("(set-logic QF_LIA)");
    scan("(declare-fun x () Int)");
    scan("(declare-fun y () Int)");
    scan("(assert (= (+ x (* 2 y)) 20))");
    scan("(push 1)");
    scan("(assert (= (- x y) 2))");
    scan("(check-sat)");
    scan("(pop 1)");
    scan("(push 1)");
    scan("(assert (= (- x y) 3))");
    scan("(check-sat)");
    scan("(pop 1)");
    scan("(exit)");
    std::cout << "=======================" << std::endl << std::endl;
}

static void tst7() {
    std::cout << "Defining new sorts, SMT-LIBv2 Tutorial " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(set-option :print-success false)");
    scan("(set-logic QF_UF)");
    scan("(declare-sort A 0)");
    scan("(declare-fun a () A)");
    scan("(declare-fun b () A)");
    scan("(declare-fun c () A)");
    scan("(declare-fun d () A)");
    scan("(declare-fun e () A)");
    scan("(assert (or (= c a)(= c b)))");
    scan("(assert (or (= d a)(= d b)))");
    scan("(assert (or (= e a)(= e b)))");
    scan("(push 1)");
    scan("(distinct c d)");
    scan("(check-sat)");
    scan("(pop 1)");
    scan("(push 1)");
    scan("(distinct c d e)");
    scan("(check-sat)");
    scan("(pop 1)");
    scan("(exit)");
    std::cout << "=======================" << std::endl << std::endl;
}

static void tst8() {
    std::cout << "Giving Information, SMT-LIBv2 Tutorial " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(get-info :name)");
    scan("(exit)");
    std::cout << "=======================" << std::endl << std::endl;
}

//     try {
//         scan("(* (* foo *)");
//         lean_unreachable();
//     } catch (exception const & ex) {
//         std::cout << "expected error: " << ex.what() << "\n";
//     }

// static void tst2() {
//     scan("x::name");
//     scan("x::10::foo");
//     check("x::name", {st::Symbol});
// //    check("fun (x : Bool), x", {st::Lambda, st::LeftParen, st::Symbol, st::Colon, st::Symbol, st::RightParen, st::Comma, st::Symbol});
//     check("+++", {st::Symbol});
//     check("x+y", {st::Symbol, st::Symbol, st::Symbol});
//     check("(* testing *)", {});
//     check(" 2.31  ", {st::DecVal});
//     check(" 333 22", {st::NumVal, st::NumVal});
// //    check("Int -> Int", {st::Symbol, st::Arrow, st::Symbol});
// //    check("Int --> Int", {st::Symbol, st::Symbol, st::Symbol});
//     check("x := 10", {st::Symbol, st::Assign, st::NumVal});
//     check("(x+1):Int", {st::LeftParen, st::Symbol, st::Symbol, st::NumVal, st::RightParen, st::Colon, st::Symbol});
//     check("{x}", {st::LeftCurlyBracket, st::Symbol, st::RightCurlyBracket});
// //    check("\u03BB \u03A0 \u2192", {st::Lambda, st::Pi, st::Arrow});
//     scan("++\u2295++x\u2296\u2296");
//     check("++\u2295++x\u2296\u2296", {st::Symbol, st::Symbol, st::Symbol, st::Symbol, st::Symbol});
//     scan("x10");
//     check_name("x10", name("x10"));
//     check_name("x::10", name(name("x"), 10));
//     check_name("x::10::bla::0", name(name(name(name("x"), 10), "bla"), 0u));
//     check("0::1", {st::NumVal, st::Colon, st::Colon, st::NumVal});
//     check_name("\u2296\u2296", name("\u2296\u2296"));
//     try {
//         scan("x::1000000000000000000");
//         lean_unreachable();
//     } catch (exception const & ex) {
//         std::cout << "expected error: " << ex.what() << "\n";
//     }
//     scan("Theorem a : Bool Axiom b : Int", list<name>({"Theorem", "Axiom"}));
//     check("Theorem a : Bool Axiom b : Int", {st::CommandId, st::Symbol, st::Colon, st::Symbol, st::CommandId, st::Symbol, st::Colon, st::Symbol}, list<name>({"Theorem", "Axiom"}));
//     scan("foo \"tst\\\"\" : Int");
//     check("foo \"tst\\\"\" : Int", {st::Symbol, st::StringVal, st::Colon, st::Symbol});
//     try {
//         scan("\"foo");
//         lean_unreachable();
//     } catch (exception const & ex) {
//         std::cout << "expected error: " << ex.what() << "\n";
//     }
//     scan("2.13 1.2 0.5");
// }

int main() {
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    tst7();
    tst8();
    return has_violations() ? 1 : 0;
}
