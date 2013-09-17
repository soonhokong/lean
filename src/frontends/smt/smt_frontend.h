/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "environment.h"
#include "state.h"
#include "smt_operator_info.h"

namespace lean {
namespace smt {
/**
   \brief Object for managing the environment, parser, pretty printer,
   elaborator, etc.
*/
class frontend {
    struct imp;
    std::shared_ptr<imp> m_imp;
    explicit frontend(imp * new_ptr);
    explicit frontend(std::shared_ptr<imp> const & ptr);
    state & get_state_core();
public:
    frontend();
    ~frontend();

    /**
       @name Parent/Child frontend management.
    */
    /*@{*/
    /**
        \brief Create a child environment. This frontend object will
        only allow "read-only" operations until all children frontend
        objects are deleted.
    */
    frontend mk_child() const;

    /** \brief Return true iff this fronted has children frontend. */
    bool has_children() const;

    /** \brief Return true iff this frontend has a parent frontend. */
    bool has_parent() const;

    /** \brief Return parent frontend */
    frontend parent() const;
    /*@}*/

    /**
       @name Environment API
    */
    /*@{*/
    /** \brief Coercion frontend -> environment. */
    environment const & get_environment() const;
    operator environment const &() const { return get_environment(); }

    level add_uvar(name const & n, level const & l);
    level add_uvar(name const & n);
    level get_uvar(name const & n) const;
    void add_definition(name const & n, expr const & t, expr const & v, bool opaque = false);
    void add_theorem(name const & n, expr const & t, expr const & v);
    void add_definition(name const & n, expr const & v, bool opaque = false);
    void add_axiom(name const & n, expr const & t);
    void add_var(name const & n, expr const & t);
    object const & get_object(name const & n) const;
    object const & find_object(name const & n) const;
    bool has_object(name const & n) const;
    typedef environment::object_iterator object_iterator;
    object_iterator begin_objects() const;
    object_iterator end_objects() const;
    object_iterator begin_local_objects() const;
    object_iterator end_local_objects() const;
    /*@}*/

    /**
       @name Notation for parsing and pretty printing.
    */
    /*@{*/
    void add_infix(name const & opn, unsigned precedence, expr const & d);
    void add_infixl(name const & opn, unsigned precedence, expr const & d);
    void add_infixr(name const & opn, unsigned precedence, expr const & d);
    void add_prefix(name const & opn, unsigned precedence, expr const & d);
    void add_postfix(name const & opn, unsigned precedence, expr const & d);
    void add_mixfixl(unsigned sz, name const * opns, unsigned precedence, expr const & d);
    void add_mixfixr(unsigned sz, name const * opns, unsigned precedence, expr const & d);
    void add_mixfixc(unsigned sz, name const * opns, unsigned precedence, expr const & d);
    /**
        \brief Return the operator (if one exists) associated with the
        given expression.

        \remark If an operator is not associated with \c e, then
        return the null operator.

        \remark This is used for pretty printing.
    */
    operator_info find_op_for(expr const & e) const;
    /**
       \brief Return the operator (if one exists) that can appear at
       the beginning of a language construct.

        \remark If there isn't a nud operator starting with \c n, then
        return the null operator.

        \remark This is used for parsing.
    */
    operator_info find_nud(name const & n) const;
    /**
       \brief Return the operator (if one exists) that can appear
       inside of a language construct.

        \remark If there isn't a led operator starting with \c n, then
        return the null operator.

        \remark This is used for parsing.
    */
    operator_info find_led(name const & n) const;
    /*@}*/

    /**
       @name State management.
    */
    /*@{*/
    state const & get_state() const;
    operator state const &() const { return get_state(); }
    void set_options(options const & opts);
    template<typename T> void set_option(name const & n, T const & v) { get_state_core().set_option(n, v); }
    void set_regular_channel(std::shared_ptr<output_channel> const & out);
    void set_diagnostic_channel(std::shared_ptr<output_channel> const & out);
    /*@}*/

    /**
       @name Interrupts.
    */
    void set_interrupt(bool flag);
    void interrupt() { set_interrupt(true); }
    void reset_interrupt() { set_interrupt(false); }
    /*@}*/
};
}
}
