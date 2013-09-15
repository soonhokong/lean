/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Leonardo de Moura
*/
#include <sstream>
#include <string>
#include "util/test.h"
#include "util/exception.h"
#include "util/escaped.h"
#include "frontends/smt/scanner.h"

using namespace lean;
using namespace smt;

#define st scanner::token

#ifdef _0
static std::string token_to_string(scanner::token const & t) {
    switch (t) {
    case scanner::token::LeftParen:         return "st::LeftParen";
    case scanner::token::RightParen:        return "st::RightParen";
    case scanner::token::Keyword:           return "st::Keyword";
    case scanner::token::Symbol:            return "st::Symbol";
    case scanner::token::StringVal:         return "st::StringVal";
    case scanner::token::NumVal:            return "st::NumVal";
    case scanner::token::BinVal:            return "st::BinVal";
    case scanner::token::HexVal:            return "st::HexVal";
    case scanner::token::DecVal:            return "st::DecVal";
    case scanner::token::Eof:               return "st::Eof";
    default:
        return "Error in toekn_to_string";
    }
}

static void scan_for_check_answer(char const * str) {
    std::cout << "check(\"" << escaped(str) << "\", " << std::endl;
    std::cout << "\t{";
    std::istringstream in(str);
    scanner s(in);
    while (true) {
        st t = s.scan();
        if (t == st::Eof)
            break;
        std::cout << token_to_string(t);
        std::cout << ", ";
    }
    std::cout << "});" << std::endl;
}
#endif

static void scan(char const * str) {
    std::cout << str << std::endl;
    std::cout << "=> ";
    std::istringstream in(str);
    scanner s(in);
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

static void check(char const * str, std::initializer_list<scanner::token> const & l) {
    auto it = l.begin();
    std::istringstream in(str);
    scanner s(in);
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

static void tst1() {
    std::cout << "1. Basic Boolean Example, SMT-LIBv2 Tutorial " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(set-logic QF_UF)");
    scan("(declare-fun p () Bool)");
    scan("(assert (and p (not p)))");
    scan("(check-sat)");
    scan("(exit)");

    check("(set-logic QF_UF)",
          {st::LeftParen, st::Symbol, st::Symbol, st::RightParen});
    check("(declare-fun p () Bool)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(assert (and p (not p)))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::RightParen, st::RightParen, st::RightParen});
    check("(check-sat)",
          {st::LeftParen, st::Symbol, st::RightParen});
    check("(exit)",
          {st::LeftParen, st::Symbol, st::RightParen});
    std::cout << "=======================" << std::endl << std::endl;
}

static void tst2() {
    std::cout << "2. Selecting options, SMT-LIBv2 Tutorial " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(set-option :print-success false)");
    scan("(set-logic QF_UF)");
    scan("(declare-fun p () Bool)");
    scan("(assert (and p (not p)))");
    scan("(check-sat)");
    scan("(exit)");
    std::cout << "=======================" << std::endl << std::endl;

    check("(set-option :print-success false)",
          {st::LeftParen, st::Symbol, st::Keyword, st::Symbol, st::RightParen});
    check("(set-logic QF_UF)",
          {st::LeftParen, st::Symbol, st::Symbol, st::RightParen});
    check("(declare-fun p () Bool)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(assert (and p (not p)))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::RightParen, st::RightParen, st::RightParen});
    check("(check-sat)",
          {st::LeftParen, st::Symbol, st::RightParen});
    check("(exit)",
          {st::LeftParen, st::Symbol, st::RightParen});
}

static void tst3() {
    std::cout << "3. Integer Arithmetic - 1, SMT-LIBv2 Tutorial " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(set-logic QF_LIA)");
    scan("(declare-fun x () Int)");
    scan("(declare-fun y () Int)");
    scan("(assert (= (+ x (* 2 y)) 20))");
    scan("(assert (= (- x y) 2))");
    scan("(check-sat)");
    scan("(exit)");
    std::cout << "=======================" << std::endl << std::endl;

    check("(set-logic QF_LIA)",
          {st::LeftParen, st::Symbol, st::Symbol, st::RightParen});
    check("(declare-fun x () Int)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun y () Int)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(assert (= (+ x (* 2 y)) 20))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::Symbol, st::NumVal, st::Symbol, st::RightParen, st::RightParen, st::NumVal, st::RightParen, st::RightParen});
    check("(assert (= (- x y) 2))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::NumVal, st::RightParen, st::RightParen});
    check("(check-sat)",
          {st::LeftParen, st::Symbol, st::RightParen});
    check("(exit)",
          {st::LeftParen, st::Symbol, st::RightParen});
}

static void tst4() {
    std::cout << "4. Integer Arithmetic - 2, SMT-LIBv2 Tutorial " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(set-logic QF_LIA)");
    scan("(declare-fun x () Int)");
    scan("(declare-fun y () Int)");
    scan("(assert (= (+ x (* 2 y)) 20))");
    scan("(assert (= (- x y) 3))");
    scan("(check-sat)");
    scan("(exit)");
    std::cout << "=======================" << std::endl << std::endl;

    check("(set-logic QF_LIA)",
          {st::LeftParen, st::Symbol, st::Symbol, st::RightParen});
    check("(declare-fun x () Int)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun y () Int)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(assert (= (+ x (* 2 y)) 20))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::Symbol, st::NumVal, st::Symbol, st::RightParen, st::RightParen, st::NumVal, st::RightParen, st::RightParen});
    check("(assert (= (- x y) 3))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::NumVal, st::RightParen, st::RightParen});
    check("(check-sat)",
          {st::LeftParen, st::Symbol, st::RightParen});
    check("(exit)",
          {st::LeftParen, st::Symbol, st::RightParen});
}

static void tst5() {
    std::cout << "5. Getting values, SMT-LIBv2 Tutorial " << std::endl;
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

    check("(set-option :print-success false)",
          {st::LeftParen, st::Symbol, st::Keyword, st::Symbol, st::RightParen});
    check("(set-option :produce-models true)",
          {st::LeftParen, st::Symbol, st::Keyword, st::Symbol, st::RightParen});
    check("(set-option :interactive-mode true)",
          {st::LeftParen, st::Symbol, st::Keyword, st::Symbol, st::RightParen});
    check("(set-logic QF_LIA)",
          {st::LeftParen, st::Symbol, st::Symbol, st::RightParen});
    check("(declare-fun x () Int)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun y () Int)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(assert (= (+ x (* 2 y)) 20))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::Symbol, st::NumVal, st::Symbol, st::RightParen, st::RightParen, st::NumVal, st::RightParen, st::RightParen});
    check("(assert (= (- x y) 2))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::NumVal, st::RightParen, st::RightParen});
    check("(check-sat)",
          {st::LeftParen, st::Symbol, st::RightParen});
    check("(get-value (x y))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::RightParen, st::RightParen});
    check("(exit)",
          {st::LeftParen, st::Symbol, st::RightParen});
}

static void tst6() {
    std::cout << "6. Using scopes to explore multiple problems, SMT-LIBv2 Tutorial " << std::endl;
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

    check("(set-option :print-success false)",
          {st::LeftParen, st::Symbol, st::Keyword, st::Symbol, st::RightParen});
    check("(set-logic QF_LIA)",
          {st::LeftParen, st::Symbol, st::Symbol, st::RightParen});
    check("(declare-fun x () Int)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun y () Int)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(assert (= (+ x (* 2 y)) 20))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::Symbol, st::NumVal, st::Symbol, st::RightParen, st::RightParen, st::NumVal, st::RightParen, st::RightParen});
    check("(push 1)",
          {st::LeftParen, st::Symbol, st::NumVal, st::RightParen});
    check("(assert (= (- x y) 2))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::NumVal, st::RightParen, st::RightParen});
    check("(check-sat)",
          {st::LeftParen, st::Symbol, st::RightParen});
    check("(pop 1)",
          {st::LeftParen, st::Symbol, st::NumVal, st::RightParen});
    check("(push 1)",
          {st::LeftParen, st::Symbol, st::NumVal, st::RightParen});
    check("(assert (= (- x y) 3))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::NumVal, st::RightParen, st::RightParen});
    check("(check-sat)",
          {st::LeftParen, st::Symbol, st::RightParen});
    check("(pop 1)",
          {st::LeftParen, st::Symbol, st::NumVal, st::RightParen});
    check("(exit)",
          {st::LeftParen, st::Symbol, st::RightParen});
}

static void tst7() {
    std::cout << "7. Defining new sorts, SMT-LIBv2 Tutorial " << std::endl;
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

    check("(set-option :print-success false)",
          {st::LeftParen, st::Symbol, st::Keyword, st::Symbol, st::RightParen});
    check("(set-logic QF_UF)",
          {st::LeftParen, st::Symbol, st::Symbol, st::RightParen});
    check("(declare-sort A 0)",
          {st::LeftParen, st::Symbol, st::Symbol, st::NumVal, st::RightParen});
    check("(declare-fun a () A)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun b () A)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun c () A)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun d () A)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun e () A)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(assert (or (= c a)(= c b)))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::RightParen, st::RightParen});
    check("(assert (or (= d a)(= d b)))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::RightParen, st::RightParen});
    check("(assert (or (= e a)(= e b)))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::RightParen, st::RightParen});
    check("(push 1)",
          {st::LeftParen, st::Symbol, st::NumVal, st::RightParen});
    check("(distinct c d)",
          {st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen});
    check("(check-sat)",
          {st::LeftParen, st::Symbol, st::RightParen});
    check("(pop 1)",
          {st::LeftParen, st::Symbol, st::NumVal, st::RightParen});
    check("(push 1)",
          {st::LeftParen, st::Symbol, st::NumVal, st::RightParen});
    check("(distinct c d e)",
          {st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::Symbol, st::RightParen});
    check("(check-sat)",
          {st::LeftParen, st::Symbol, st::RightParen});
    check("(pop 1)",
          {st::LeftParen, st::Symbol, st::NumVal, st::RightParen});
    check("(exit)",
          {st::LeftParen, st::Symbol, st::RightParen});
}

static void tst8() {
    std::cout << "8. Giving Information, SMT-LIBv2 Tutorial " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(get-info :name)");
    scan("(exit)");
    std::cout << "=======================" << std::endl << std::endl;

    check("(get-info :name)",
          {st::LeftParen, st::Symbol, st::Keyword, st::RightParen});
    check("(exit)",
          {st::LeftParen, st::Symbol, st::RightParen});
}

static void tst9() {
    std::cout << "9. Parametric definition" << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(set-logic QF_UF)");
    scan("(declare-sort A 0) ; a new sort named A");
    scan("(declare-sort B 0) ; a new sort named B");
    scan("(declare-fun a1 () A) ; a new constant of sort A");
    scan("(declare-fun a2 () A) ; another constant of sort A");
    scan("(declare-fun b1 () B) ; a new constant of sort B");
    scan("(declare-fun b2 () B) ; another constant of sort B");
    scan("(assert (= a1 a2)) ; comparing values of sort A");
    scan("(assert (= b1 b2)) ; comparing values of sort B");
    scan("(assert (= a1 b1)) ; ILLEGAL - a1 and b1 have different sorts");
    std::cout << "=======================" << std::endl << std::endl;

    check("(set-logic QF_UF)",
          {st::LeftParen, st::Symbol, st::Symbol, st::RightParen});
    check("(declare-sort A 0) ; a new sort named A",
          {st::LeftParen, st::Symbol, st::Symbol, st::NumVal, st::RightParen});
    check("(declare-sort B 0) ; a new sort named B",
          {st::LeftParen, st::Symbol, st::Symbol, st::NumVal, st::RightParen});
    check("(declare-fun a1 () A) ; a new constant of sort A",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun a2 () A) ; another constant of sort A",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun b1 () B) ; a new constant of sort B",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun b2 () B) ; another constant of sort B",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(assert (= a1 a2)) ; comparing values of sort A",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::RightParen});
    check("(assert (= b1 b2)) ; comparing values of sort B",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::RightParen});
    check("(assert (= a1 b1)) ; ILLEGAL - a1 and b1 have different sorts",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::RightParen});
}

static void tst10() {
    std::cout << "10. Multiple definition " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(set-logic AUFLIRA)");
    scan("(assert (= (+ 1 2) 3)) ; adding two Ints");
    scan("(assert (= (+ 1.0 2.0) 3.0) ; adding two Reals");
    scan("(assert (= (+ 1 2.0) 3.0) ; ILLEGAL - mixed sorts");
    std::cout << "=======================" << std::endl << std::endl;

    check("(set-logic AUFLIRA)",
          {st::LeftParen, st::Symbol, st::Symbol, st::RightParen});
    check("(assert (= (+ 1 2) 3)) ; adding two Ints",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::NumVal, st::NumVal, st::RightParen, st::NumVal, st::RightParen, st::RightParen});
    check("(assert (= (+ 1.0 2.0) 3.0) ; adding two Reals",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::DecVal, st::DecVal, st::RightParen, st::DecVal, st::RightParen});
    check("(assert (= (+ 1 2.0) 3.0) ; ILLEGAL - mixed sorts",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::NumVal, st::DecVal, st::RightParen, st::DecVal, st::RightParen});
}

static void tst11() {
    std::cout << "11. Overloading on result sort " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(declare-fun listi () (List Int)) ; listi is a List of Int");
    scan("(assert (= listb (as emptylist (List Bool))))  ; use the definition of emptylist that has (List Bool) result");
    scan("(assert (= listi (as emptylist (List Int))))   ; use the definition of emptylist that has (List Int) result");
    scan("(assert (= listb emptylist)); ILLEGAL - have to specify the sort of the overloaded constant");
    scan("(assert (= listb (as emptylist (List Int)))) ; ILLEGAL - sort mismatch");
    std::cout << "=======================" << std::endl << std::endl;

    check("(declare-fun listi () (List Int)) ; listi is a List of Int",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::LeftParen, st::Symbol, st::Symbol, st::RightParen, st::RightParen});
    check("(assert (= listb (as emptylist (List Bool))))  ; use the definition of emptylist that has (List Bool) result",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::RightParen, st::RightParen, st::RightParen, st::RightParen});
    check("(assert (= listi (as emptylist (List Int))))   ; use the definition of emptylist that has (List Int) result",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::RightParen, st::RightParen, st::RightParen, st::RightParen});
    check("(assert (= listb emptylist)); ILLEGAL - have to specify the sort of the overloaded constant",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::RightParen});
    check("(assert (= listb (as emptylist (List Int)))) ; ILLEGAL - sort mismatch",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::RightParen, st::RightParen, st::RightParen, st::RightParen});
}

static void tst12() {
    std::cout << "12. Quantifiers " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("( forall ((x Int)) (> (p x) 0) )");
    scan("( exists ((x Int)(y Int)) (and (> (+ x y) 0) (< (- x y) 0)))");
    std::cout << "=======================" << std::endl << std::endl;

    check("( forall ((x Int)) (> (p x) 0) )",
          {st::LeftParen, st::Symbol, st::LeftParen, st::LeftParen, st::Symbol, st::Symbol, st::RightParen, st::RightParen, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::RightParen, st::NumVal, st::RightParen, st::RightParen});
    check("( exists ((x Int)(y Int)) (and (> (+ x y) 0) (< (- x y) 0)))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::LeftParen, st::Symbol, st::Symbol, st::RightParen, st::LeftParen, st::Symbol, st::Symbol, st::RightParen, st::RightParen, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::NumVal, st::RightParen, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::NumVal, st::RightParen, st::RightParen, st::RightParen});
}

static void tst13() {
    std::cout << "13. Let " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("( let ( (a (+ x y)) (b (- x y)) ) (+ a b))");
    scan("( let ( (x (+ x y)) (y (- x y)) ) ( + x y))");
    std::cout << "=======================" << std::endl << std::endl;

    check("( let ( (a (+ x y)) (b (- x y)) ) (+ a b))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::RightParen, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::RightParen, st::RightParen, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::RightParen});
    check("( let ( (x (+ x y)) (y (- x y)) ) ( + x y))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::RightParen, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::RightParen, st::RightParen, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::RightParen});
}

static void tst14() {
    std::cout << "14. Attributes " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(assert (> (!  (+ x y) :named sum) 0))");
    scan("(assert (>= (! (+ x y) :named sum) sum)");
    scan("(assert (>= sum (! (+ x y) :named sum))) ; Illegal");
    std::cout << "=======================" << std::endl << std::endl;

    check("(assert (> (!  (+ x y) :named sum) 0))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::Keyword, st::Symbol, st::RightParen, st::NumVal, st::RightParen, st::RightParen});
    check("(assert (>= (! (+ x y) :named sum) sum)",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::Keyword, st::Symbol, st::RightParen, st::Symbol, st::RightParen});
    check("(assert (>= sum (! (+ x y) :named sum))) ; Illegal",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::Keyword, st::Symbol, st::RightParen, st::RightParen, st::RightParen});
}

static void tst15() {
    std::cout << "15. declare-sort " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(declare-sort MySort 0) ; new sort named MySort success");
    scan("(declare-fun x () MySort) ; using MySort as the sort of a new constant success");
    scan("(declare-sort Pair 2)");
    scan("(Pair X X)");
    scan("(Pair X Y)");
    scan("(Pair Y Y)");
    std::cout << "=======================" << std::endl << std::endl;

    check("(declare-sort MySort 0) ; new sort named MySort success",
          {st::LeftParen, st::Symbol, st::Symbol, st::NumVal, st::RightParen});
    check("(declare-fun x () MySort) ; using MySort as the sort of a new constant success",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-sort Pair 2)",
          {st::LeftParen, st::Symbol, st::Symbol, st::NumVal, st::RightParen});
    check("(Pair X X)",
          {st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen});
    check("(Pair X Y)",
          {st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen});
    check("(Pair Y Y)",
          {st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen});
}

static void tst16() {
    std::cout << "16. define-fun / declare-fun" << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(declare-fun size ( (Array Int Bool) ) Int)");
    scan("(define-fun av ((p Int)(q Int)) Bool (or (> p (+ q 2)) (< p (- q 2))))");
    std::cout << "=======================" << std::endl << std::endl;

    check("(declare-fun size ( (Array Int Bool) ) Int)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::RightParen, st::Symbol, st::RightParen});
    check("(define-fun av ((p Int)(q Int)) Bool (or (> p (+ q 2)) (< p (- q 2))))",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::LeftParen, st::Symbol, st::Symbol, st::RightParen, st::LeftParen, st::Symbol, st::Symbol, st::RightParen, st::RightParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::NumVal, st::RightParen, st::RightParen, st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::NumVal, st::RightParen, st::RightParen, st::RightParen, st::RightParen});
}

static void tst17() {
    std::cout << "17. get-value " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(set-option :produce-models true)");
    scan("(set-logic QF_LIA)");
    scan("(declare-fun x () Int)");
    scan("(declare-fun y () Int)");
    scan("(assert (= (+ x y) 9))");
    scan("(assert (= (+ (* 2 x) (* 3 y)) 22))");
    scan("(check-sat)");
    scan("(get-value (x))");
    scan("(get-value ((- x y) (+ 2 y)))");
    std::cout << "=======================" << std::endl << std::endl;

    check("(declare-fun size ( (Array Int Bool) ) Int)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::RightParen, st::Symbol, st::RightParen});
    check("(define-fun av ((p Int)(q Int)) Bool (or (> p (+ q 2)) (< p (- q 2))))",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::LeftParen, st::Symbol, st::Symbol, st::RightParen, st::LeftParen, st::Symbol, st::Symbol, st::RightParen, st::RightParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::NumVal, st::RightParen, st::RightParen, st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::NumVal, st::RightParen, st::RightParen, st::RightParen, st::RightParen});
}

static void tst18() {
    std::cout << "18. get-assignment " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(set-option :produce-assignments true)");
    scan("(set-logic QF_UF)");
    scan("(declare-fun p () Bool)");
    scan("(declare-fun q () Bool)");
    scan("(declare-fun r () Bool)");
    scan("(assert (not (=> (or (!  p :named P) (!  q :named Q)) (!  r :named R))))");
    scan("(check-sat)");
    scan("(get-assignment)");
    std::cout << "=======================" << std::endl << std::endl;

    check("(set-option :produce-assignments true)",
          {st::LeftParen, st::Symbol, st::Keyword, st::Symbol, st::RightParen});
    check("(set-logic QF_UF)",
          {st::LeftParen, st::Symbol, st::Symbol, st::RightParen});
    check("(declare-fun p () Bool)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun q () Bool)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun r () Bool)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(assert (not (=> (or (!  p :named P) (!  q :named Q)) (!  r :named R))))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Keyword, st::Symbol, st::RightParen, st::LeftParen, st::Symbol, st::Symbol, st::Keyword, st::Symbol, st::RightParen, st::RightParen, st::LeftParen, st::Symbol, st::Symbol, st::Keyword, st::Symbol, st::RightParen, st::RightParen, st::RightParen, st::RightParen});
    check("(check-sat)",
          {st::LeftParen, st::Symbol, st::RightParen});
    check("(get-assignment)",
          {st::LeftParen, st::Symbol, st::RightParen});
}

static void tst19() {
    std::cout << "19. get-proof " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(set-option :produce-proofs true)");
    scan("(set-logic QF_UF)");
    scan("(declare-fun p () Bool)");
    scan("(declare-fun q () Bool)");
    scan("(declare-fun r () Bool)");
    scan("(assert (=> p q))");
    scan("(assert (=> q r))");
    scan("(assert (not (=> p r)))");
    scan("(check-sat)");
    scan("(get-proof)");
    std::cout << "=======================" << std::endl << std::endl;

    check("(set-option :produce-proofs true)",
          {st::LeftParen, st::Symbol, st::Keyword, st::Symbol, st::RightParen});
    check("(set-logic QF_UF)",
          {st::LeftParen, st::Symbol, st::Symbol, st::RightParen});
    check("(declare-fun p () Bool)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun q () Bool)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun r () Bool)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(assert (=> p q))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::RightParen});
    check("(assert (=> q r))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::RightParen});
    check("(assert (not (=> p r)))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::RightParen, st::RightParen});
    check("(check-sat)",
          {st::LeftParen, st::Symbol, st::RightParen});
    check("(get-proof)",
          {st::LeftParen, st::Symbol, st::RightParen});
}

static void tst20() {
    std::cout << "20. get-unsat-core  " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(set-option :produce-unsat-cores true)");
    scan("(set-logic QF_UF)");
    scan("(declare-fun p () Bool)");
    scan("(declare-fun q () Bool)");
    scan("(declare-fun r () Bool)");
    scan("(declare-fun s () Bool)");
    scan("(declare-fun t () Bool)");
    scan("(assert (!  (=> p q) :named PQ))");
    scan("(assert (!  (=> q r) :named QR))");
    scan("(assert (!  (=> r s) :named RS))");
    scan("(assert (!  (=> s t) :named ST))");
    scan("(assert (!  (not (=> q s)) :named NQS))");
    scan("(check-sat)");
    scan("(get-unsat-core)");
    std::cout << "=======================" << std::endl << std::endl;

    check("(set-option :produce-unsat-cores true)",
          {st::LeftParen, st::Symbol, st::Keyword, st::Symbol, st::RightParen});
    check("(set-logic QF_UF)",
          {st::LeftParen, st::Symbol, st::Symbol, st::RightParen});
    check("(declare-fun p () Bool)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun q () Bool)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun r () Bool)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun s () Bool)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun t () Bool)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(assert (!  (=> p q) :named PQ))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::Keyword, st::Symbol, st::RightParen, st::RightParen});
    check("(assert (!  (=> q r) :named QR))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::Keyword, st::Symbol, st::RightParen, st::RightParen});
    check("(assert (!  (=> r s) :named RS))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::Keyword, st::Symbol, st::RightParen, st::RightParen});
    check("(assert (!  (=> s t) :named ST))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::Keyword, st::Symbol, st::RightParen, st::RightParen});
    check("(assert (!  (not (=> q s)) :named NQS))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::RightParen, st::Keyword, st::Symbol, st::RightParen, st::RightParen});
    check("(check-sat)",
          {st::LeftParen, st::Symbol, st::RightParen});
    check("(get-unsat-core)",
          {st::LeftParen, st::Symbol, st::RightParen});
}

static void tst21() {
    std::cout << "21. push & pop " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(set-logic QF_LIA)");
    scan("(declare-fun x () Int) ; declare some constants");
    scan("(declare-fun y () Int)");
    scan("(declare-fun z () Int)");
    scan("(push 1)");
    scan("(assert (= (+ x y) 10))");
    scan("(assert (= (+ x (* 2 y)) 20))");
    scan("(check-sat)");
    scan("(pop 1) ; clear the assertions");
    scan("(push 1) ; ready for another problem");
    scan("(assert (= (+ (* 3 x) y) 10))");
    scan("(assert (= (+ (* 2 x) (* 2 y)) 21))");
    scan("(check-sat)");
    scan("(declare-fun p () Bool)");
    scan("(pop 1)");
    scan("(assert p)");
    std::cout << "=======================" << std::endl << std::endl;

    check("(set-logic QF_LIA)",
          {st::LeftParen, st::Symbol, st::Symbol, st::RightParen});
    check("(declare-fun x () Int) ; declare some constants",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun y () Int)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun z () Int)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(push 1)",
          {st::LeftParen, st::Symbol, st::NumVal, st::RightParen});
    check("(assert (= (+ x y) 10))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::NumVal, st::RightParen, st::RightParen});
    check("(assert (= (+ x (* 2 y)) 20))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::Symbol, st::NumVal, st::Symbol, st::RightParen, st::RightParen, st::NumVal, st::RightParen, st::RightParen});
    check("(check-sat)",
          {st::LeftParen, st::Symbol, st::RightParen});
    check("(pop 1) ; clear the assertions",
          {st::LeftParen, st::Symbol, st::NumVal, st::RightParen});
    check("(push 1) ; ready for another problem",
          {st::LeftParen, st::Symbol, st::NumVal, st::RightParen});
    check("(assert (= (+ (* 3 x) y) 10))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::NumVal, st::Symbol, st::RightParen, st::Symbol, st::RightParen, st::NumVal, st::RightParen, st::RightParen});
    check("(assert (= (+ (* 2 x) (* 2 y)) 21))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::NumVal, st::Symbol, st::RightParen, st::LeftParen, st::Symbol, st::NumVal, st::Symbol, st::RightParen, st::RightParen, st::NumVal, st::RightParen, st::RightParen});
    check("(check-sat)",
          {st::LeftParen, st::Symbol, st::RightParen});
    check("(declare-fun p () Bool)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(pop 1)",
          {st::LeftParen, st::Symbol, st::NumVal, st::RightParen});
    check("(assert p)",
          {st::LeftParen, st::Symbol, st::Symbol, st::RightParen});
}

static void tst22() {
    std::cout << "22. get-assertions " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(set-option :interactive-mode true)");
    scan("(set-logic QF_UF)");
    scan("(declare-fun p () Bool)");
    scan("(declare-fun q () Bool)");
    scan("(push 1)");
    scan("(assert (or p q))");
    scan("(push 1)");
    scan("(assert (not q))");
    scan("(get-assertions)");
    scan("(pop 1)");
    scan("(get-assertions)");
    scan("(pop 1)");
    scan("(get-assertions)");
    std::cout << "=======================" << std::endl << std::endl;

    check("(set-option :interactive-mode true)",
          {st::LeftParen, st::Symbol, st::Keyword, st::Symbol, st::RightParen});
    check("(set-logic QF_UF)",
          {st::LeftParen, st::Symbol, st::Symbol, st::RightParen});
    check("(declare-fun p () Bool)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun q () Bool)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(push 1)",
          {st::LeftParen, st::Symbol, st::NumVal, st::RightParen});
    check("(assert (or p q))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::RightParen});
    check("(push 1)",
          {st::LeftParen, st::Symbol, st::NumVal, st::RightParen});
    check("(assert (not q))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::RightParen, st::RightParen});
    check("(get-assertions)",
          {st::LeftParen, st::Symbol, st::RightParen});
    check("(pop 1)",
          {st::LeftParen, st::Symbol, st::NumVal, st::RightParen});
    check("(get-assertions)",
          {st::LeftParen, st::Symbol, st::RightParen});
    check("(pop 1)",
          {st::LeftParen, st::Symbol, st::NumVal, st::RightParen});
    check("(get-assertions)",
          {st::LeftParen, st::Symbol, st::RightParen});
}

static void tst23() {
    std::cout << "23. get-option / set-option " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(get-option :print-success)");
    scan("(set-option :print-success false)");
    scan("(get-option :print-success)");
    scan("(set-option :print-success true)");
    std::cout << "=======================" << std::endl << std::endl;

    check("(get-option :print-success)",
          {st::LeftParen, st::Symbol, st::Keyword, st::RightParen});
    check("(set-option :print-success false)",
          {st::LeftParen, st::Symbol, st::Keyword, st::Symbol, st::RightParen});
    check("(get-option :print-success)",
          {st::LeftParen, st::Symbol, st::Keyword, st::RightParen});
    check("(set-option :print-success true)",
          {st::LeftParen, st::Symbol, st::Keyword, st::Symbol, st::RightParen});
}

static void tst24() {
    std::cout << "24. expand-definition " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("(set-option :produce-models true)");
    scan("(set-logic QF_LIA)");
    scan("(declare-fun x () Int)");
    scan("(declare-fun y () Int)");
    scan("(define-fun diff () Int (- x y))");
    scan("(assert (= (+ x y) 9))");
    scan("(assert (= (+ (* 2 x) (* 3 y)) 22))");
    scan("(check-sat)");
    scan("(set-option :expand-definitions false)");
    scan("(get-value (diff))");
    scan("(set-option :expand-definitions true)");
    scan("(get-value (diff))");
    std::cout << "=======================" << std::endl << std::endl;

    check("(set-option :produce-models true)",
          {st::LeftParen, st::Symbol, st::Keyword, st::Symbol, st::RightParen});
    check("(set-logic QF_LIA)",
          {st::LeftParen, st::Symbol, st::Symbol, st::RightParen});
    check("(declare-fun x () Int)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(declare-fun y () Int)",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::RightParen});
    check("(define-fun diff () Int (- x y))",
          {st::LeftParen, st::Symbol, st::Symbol, st::LeftParen, st::RightParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::RightParen});
    check("(assert (= (+ x y) 9))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::Symbol, st::Symbol, st::RightParen, st::NumVal, st::RightParen, st::RightParen});
    check("(assert (= (+ (* 2 x) (* 3 y)) 22))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::NumVal, st::Symbol, st::RightParen, st::LeftParen, st::Symbol, st::NumVal, st::Symbol, st::RightParen, st::RightParen, st::NumVal, st::RightParen, st::RightParen});
    check("(check-sat)",
          {st::LeftParen, st::Symbol, st::RightParen});
    check("(set-option :expand-definitions false)",
          {st::LeftParen, st::Symbol, st::Keyword, st::Symbol, st::RightParen});
    check("(get-value (diff))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::RightParen, st::RightParen});
    check("(set-option :expand-definitions true)",
          {st::LeftParen, st::Symbol, st::Keyword, st::Symbol, st::RightParen});
    check("(get-value (diff))",
          {st::LeftParen, st::Symbol, st::LeftParen, st::Symbol, st::RightParen, st::RightParen});
}

static void tst25() {
    std::cout << "25. Required Info " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("( get-info :name )");
    scan("( get-info :version )");
    scan("( get-info :authors )");
    std::cout << "=======================" << std::endl << std::endl;

    check("( get-info :name )",
          {st::LeftParen, st::Symbol, st::Keyword, st::RightParen});
    check("( get-info :version )",
          {st::LeftParen, st::Symbol, st::Keyword, st::RightParen});
    check("( get-info :authors )",
          {st::LeftParen, st::Symbol, st::Keyword, st::RightParen});
}

static void tst26() {
    std::cout << "26. set-info / get-info " << std::endl;
    std::cout << "=======================" << std::endl;
    scan("( set-info :version \"1.1\" )");
    scan("( set-info :zzz 1.1 )");
    scan("( set-info )");
    scan("( get-info :zzz)");
    std::cout << "=======================" << std::endl << std::endl;

    check("( set-info :version \"1.1\" )",
          {st::LeftParen, st::Symbol, st::Keyword, st::StringVal, st::RightParen});
    check("( set-info :zzz 1.1 )",
          {st::LeftParen, st::Symbol, st::Keyword, st::DecVal, st::RightParen});
    check("( set-info )",
          {st::LeftParen, st::Symbol, st::RightParen});
    check("( get-info :zzz)",
          {st::LeftParen, st::Symbol, st::Keyword, st::RightParen});
}

int main() {
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    tst7();
    tst8();
    tst9();
    tst10();
    tst11();
    tst12();
    tst13();
    tst14();
    tst15();
    tst16();
    tst17();
    tst18();
    tst19();
    tst20();
    tst21();
    tst22();
    tst23();
    tst24();
    tst25();
    tst26();
    return has_violations() ? 1 : 0;
}
