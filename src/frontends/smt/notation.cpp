/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
        Soonho Kong
*/
#include "kernel/builtin.h"
#include "library/basic_thms.h"
#include "library/arith/arith.h"
#include "library/cast/cast.h"
#include "frontends/smt/frontend.h"

namespace lean {
namespace smt {
/**
   \brief Initialize builtin notation.
*/
void init_builtin_notation(frontend & f) {
    std::cerr << "Add init builtin notations" << std::endl;
    f.add_prefix("not", 40, mk_not_fn());
    f.add_prefixl("and", 35, mk_and_fn());
    f.add_prefixl("or",  30, mk_or_fn());
    // f.add_prefix("xor",  30, mk_xor_fn());
    f.add_prefixr("=>",  25, mk_implies_fn());
    // f.add_prefix?("ite",  25, mk_ite_fn());
    // f.add_prefixc("=",  25, mk_eq_fn());
    // f.add_prefixp("distinct",  25, mk_distinct_fn());

    f.add_prefixc("<", 50, mk_nat_lt_fn());
    f.add_prefixc(">", 50, mk_nat_gt_fn());
    f.add_prefixc("<=", 50, mk_nat_le_fn());
    f.add_prefixc(">=", 50, mk_nat_ge_fn());

    f.add_prefixl("+", 65, mk_nat_add_fn());
    f.add_prefixl("-", 65, mk_nat_sub_fn());
    f.add_prefixl("*", 70, mk_nat_mul_fn());
}

void init_theory_ArrayEx(frontend & f) {
}

void init_logic_AUFLIA(frontend & f) {
// AUFLIA:
// Closed formulas over the theory of linear integer arithmetic and
// arrays extended with free sort and function symbols but restricted
// to arrays with integer indices and values.
}


void init_logic_AUFLIRA(frontend & f) {
// AUFLIRA:
// Closed linear formulas with free sort and function symbols over
// one- and two-dimentional arrays of integer index and real value.
}

void init_logic_AUFNIRA(frontend & f) {
// AUFNIRA:
// Closed formulas with free function and predicate symbols over a
// theory of arrays of arrays of integer index and real value.
}

void init_logic_LRA(frontend & f) {
// LRA:
// Closed linear formulas in linear real arithmetic.
}

void init_logic_QF_ABV(frontend & f) {
// QF_ABV:
// Closed quantifier-free formulas over the theory of bitvectors and bitvector arrays.
}

void init_logic_QF_AUFBV(frontend & f) {
// QF_AUFBV:
// Closed quantifier-free formulas over the theory of bitvectors and
// bitvector arrays extended with free sort and function symbols.
}

void init_logic_QFAUFLIA(frontend & f) {
// QF_AUFLIA:
// Closed quantifier-free linear formulas over the theory of integer
// arrays extended with free sort and function symbols.
}

void init_logic_QF_AX(frontend & f) {
// QF_AX:
// Closed quantifier-free formulas over the theory of arrays with extensionality.
}

void init_logic_BV(frontend & f) {
// QF_BV:
// Closed quantifier-free formulas over the theory of fixed-size bitvectors.
}

void init_logic_QF_IDL(frontend & f) {
// QF_IDL:
// Difference Logic over the integers. In essence, Boolean
// combinations of inequations of the form x - y < b where x and y are
// integer variables and b is an integer constant.
}

void init_logic_QF_LIA(frontend & f) {
// QF_LIA:
// Unquantified linear integer arithmetic. In essence, Boolean
// combinations of inequations between linear polynomials over integer
// variables.
}

void init_logic_QF_LRA(frontend & f) {
// QF_LRA:
// Unquantified linear real arithmetic. In essence, Boolean
// combinations of inequations between linear polynomials over real
// variables.
}

void init_logic_QF_NIA(frontend & f) {
// QF_NIA:
// Quantifier-free integer arithmetic.
}

void init_logic_QF_NRA(frontend & f) {
// QF_NRA:
// Quantifier-free real arithmetic.
}

void init_logic_QF_RDL(frontend & f) {
// QF_RDL:
// Difference Logic over the reals. In essence, Boolean combinations of inequations of the form x - y < b where x and y are real variables and b is a rational constant.
}

void init_logic_QF_UF(frontend & f) {
// QF_UF:
// Unquantified formulas built over a signature of uninterpreted (i.e., free) sort and function symbols.
}

void init_logic_QF_UFBV(frontend & f) {
// QF_UFBV:
// Unquantified formulas over bitvectors with uninterpreted sort function and symbols.
}

void init_logic_QF_UFIDL(frontend & f) {
// QF_UFIDL:
// Difference Logic over the integers (in essence) but with uninterpreted sort and function symbols.
}

void init_logic_QF_UFLIA(frontend & f) {
// QF_UFLIA:
// Unquantified linear integer arithmetic with uninterpreted sort and function symbols.
}

void init_logic_QF_UFLRA(frontend & f) {
// QF_UFLRA:
// Unquantified linear real arithmetic with uninterpreted sort and function symbols.
}

void init_logic_QF_UFNRA(frontend & f) {
// QF_UFNRA:
// Unquantified non-linear real arithmetic with uninterpreted sort and function symbols.
}

void init_logic_UFLRA(frontend & f) {
// UFLRA:
// Linear real arithmetic with uninterpreted sort and function symbols.
}
}
}
