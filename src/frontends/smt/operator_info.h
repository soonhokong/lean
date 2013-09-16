/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
        Soonho Kong
*/
#pragma once
#include <algorithm>
#include "util/name.h"
#include "util/list.h"
#include "util/sexpr/format.h"
#include "kernel/object.h"

namespace lean {
namespace smt {
/**
   \brief Operator fixity.
   Prefix:   ID _
   Prefixl:  ID _ _  (left associative)
             (+ a b c d)        ==> (+ (+ (+ a b) c) d)
   Prefixr:  ID _ _  (right associative)
             (=> a b c d)       ==> (=> a (=> b (=> c d)))
   Prefixc:  ID _ _  (chainable)
             (= a b c d)        ==> (and (= a b) (= b c) (= c d))
   Prefixp:  ID _ _  (pairwise)
             (distinct a b c d) ==> (and (distinct a b)
                                         (distinct a c)
                                         (distinct a d)
                                         (distinct b c)
                                         (distinct b d)
                                         (distinct c d))
   Infix:    _ ID _
   Infixl:    _ ID _    (left associative)
   Infixr:    _ ID _    (right associative)
   Postfix:  _ ID
   Mixfixl: ID _ ID _ ... ID _       (has at least two parts)
   Mixfixr: _ ID _ ID ... _ ID       (has at least two parts)
   Mixfixc: ID _ ID _ ... ID _ ID    (has at least two parts)
   Mixfixo:  _ ID _ ... ID _         (has at least two parts)
*/
enum class fixity { Prefix, Prefixl, Prefixr, Prefixc, Prefixp, Infix, Infixl, Infixr, Postfix, Mixfixl, Mixfixr, Mixfixc, Mixfixo };

/**
   \brief Data-structure for storing user defined operator
   information. This information is used during parsing and
   pretty-printing.
*/
class operator_info {
    struct imp;
    imp * m_ptr;
    explicit operator_info(imp * p);
public:
    operator_info():m_ptr(nullptr) {}
    operator_info(operator_info const & info);
    operator_info(operator_info && info);
    ~operator_info();

    operator_info & operator=(operator_info const & o);
    operator_info & operator=(operator_info && o);

    friend void swap(operator_info & o1, operator_info & o2) { std::swap(o1.m_ptr, o2.m_ptr); }

    operator bool() const { return m_ptr != nullptr; }

    friend operator_info infix(name const & op, unsigned precedence);
    friend operator_info infixl(name const & op, unsigned precedence);
    friend operator_info infixr(name const & op, unsigned precedence);
    friend operator_info prefix(name const & op, unsigned precedence);
    friend operator_info prefixl(name const & op, unsigned precedence);
    friend operator_info prefixr(name const & op, unsigned precedence);
    friend operator_info prefixc(name const & op, unsigned precedence);
    friend operator_info prefixp(name const & op, unsigned precedence);
    friend operator_info postfix(name const & op, unsigned precedence);
    friend operator_info mixfixl(unsigned num_parts, name const * parts, unsigned precedence);
    friend operator_info mixfixr(unsigned num_parts, name const * parts, unsigned precedence);
    friend operator_info mixfixc(unsigned num_parts, name const * parts, unsigned precedence);
    friend operator_info mixfixo(unsigned num_parts, name const * parts, unsigned precedence);

    /** \brief Associate a denotation (expression) with this operator. */
    void add_expr(expr const & n);

    /** \brief Return true iff the operator is overloaded. */
    bool is_overloaded() const;

    /**
       \brief Return the list of denotations for this operator.
       The list has size greater than 1 iff the operator has been
       overloaded.
       These are the possible interpretations for the operator.
    */
    list<expr> const & get_denotations() const;

    /** \brief Return the operator fixity. */
    fixity get_fixity() const;

    /** \brief Return the operator precedence. */
    unsigned get_precedence() const;

    /** \brief Return the operator name. For mixfix operators the result corresponds to the first part. */
    name const & get_op_name() const;

    /** \brief Return the operators parts. */
    list<name> const & get_op_name_parts() const;

    /** \brief Return true if all parts of the operator use only safe ASCII characters */
    bool is_safe_ascii() const;

    /** \brief Return a copy of the operator. */
    operator_info copy() const;

    friend bool operator==(operator_info const & op1, operator_info const & op2);
    friend bool operator!=(operator_info const & op1, operator_info const & op2) { return !(op1 == op2); }
};
operator_info infix(name const & op, unsigned precedence);
operator_info infixl(name const & op, unsigned precedence);
operator_info infixr(name const & op, unsigned precedence);
operator_info prefix(name const & op, unsigned precedence);
operator_info prefixl(name const & op, unsigned precedence);
operator_info prefixr(name const & op, unsigned precedence);
operator_info prefixc(name const & op, unsigned precedence);
operator_info prefixp(name const & op, unsigned precedence);
operator_info postfix(name const & op, unsigned precedence);
operator_info mixfixl(unsigned num_parts, name const * parts, unsigned precedence);
operator_info mixfixr(unsigned num_parts, name const * parts, unsigned precedence);
operator_info mixfixc(unsigned num_parts, name const * parts, unsigned precedence);
operator_info mixfixo(unsigned num_parts, name const * parts, unsigned precedence);
inline operator_info mixfixl(std::initializer_list<name> const & l, unsigned precedence) { return mixfixl(l.size(), l.begin(), precedence); }
inline operator_info mixfixr(std::initializer_list<name> const & l, unsigned precedence) { return mixfixr(l.size(), l.begin(), precedence); }
inline operator_info mixfixc(std::initializer_list<name> const & l, unsigned precedence) { return mixfixc(l.size(), l.begin(), precedence); }
inline operator_info mixfixo(std::initializer_list<name> const & l, unsigned precedence) { return mixfixo(l.size(), l.begin(), precedence); }

format pp(operator_info const & o);
std::ostream & operator<<(std::ostream & out, operator_info const & o);

/**
    \brief Create object for tracking notation/operator declarations.
    This object is mainly used for recording the declaration.
*/
class notation_declaration : public neutral_object_cell {
    operator_info m_op;
    expr          m_expr;
public:
    notation_declaration(operator_info const & op, expr const & n):m_op(op), m_expr(n) {}
    virtual ~notation_declaration() {}
    virtual char const * keyword() const;
    operator_info get_op() const { return m_op; }
    expr const & get_expr() const { return m_expr; }
};
}
}
