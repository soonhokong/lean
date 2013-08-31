/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
        Leonardo de Moura
*/
#include <unordered_map>
#include "scoped_map.h"
#include "exception.h"
#include "normalize.h"
#include "type_check.h"
#include "free_vars.h"
#include "builtin.h"
#include "arith.h"
#include "printer.h"
#include "state.h"
#include "option_declarations.h"
#include "expr_maps.h"
#include "sstream.h"
#include "kernel_exception.h"
#include "elaborator.h"
#include "smt_frontend.h"
#include "smt_parser.h"
#include "smt_scanner.h"
#include "smt_notation.h"
#include "smt_pp.h"
#ifdef LEAN_USE_READLINE
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <readline/readline.h>
#include <readline/history.h>
#endif

#ifndef SMT_DEFAULT_PARSER_PRINT_SUCCESS
#define SMT_DEFAULT_PARSER_PRINT_SUCCESS true
#endif
#ifndef SMT_DEFAULT_PARSER_EXPAND_DEFINITIONS
#define SMT_DEFAULT_PARSER_EXPAND_DEFINITIONS false
#endif
#ifndef SMT_DEFAULT_PARSER_INTERACTIVE_MODE
#define SMT_DEFAULT_PARSER_INTERACTIVE_MODE false
#endif
#ifndef SMT_DEFAULT_PARSER_PRODUCE_PROOFS
#define SMT_DEFAULT_PARSER_PRODUCE_PROOFS false
#endif
#ifndef SMT_DEFAULT_PARSER_PRODUCE_UNSAT_CORES
#define SMT_DEFAULT_PARSER_PRODUCE_UNSAT_CORES false
#endif
#ifndef SMT_DEFAULT_PARSER_PRODUCE_MODELS
#define SMT_DEFAULT_PARSER_PRODUCE_MODELS false
#endif
#ifndef SMT_DEFAULT_PARSER_PRODUCE_ASSIGNMENTS
#define SMT_DEFAULT_PARSER_PRODUCE_ASSIGNMENTS false
#endif
#ifndef SMT_DEFAULT_PARSER_REGULAR_OUTPUT_CHANNEL
#define SMT_DEFAULT_PARSER_REGULAR_OUTPUT_CHANNEL "stdout"
#endif
#ifndef SMT_DEFAULT_PARSER_DIAGNOSTIC_OUTPUT_CHANNEL
#define SMT_DEFAULT_PARSER_DIAGNOSTIC_OUTPUT_CHANNEL "stderr"
#endif
#ifndef SMT_DEFAULT_PARSER_RANDOM_SEED
#define SMT_DEFAULT_PARSER_RANDOM_SEED 0
#endif
#ifndef SMT_DEFAULT_PARSER_VERBOSITY
#define SMT_DEFAULT_PARSER_VERBOSITY 0
#endif

namespace lean {
namespace smt {
// ==========================================
// Parser configuration options

/* <option> ::= :print-success             <b_value>, default = true */
/*              :expand-definitions        <b_value>, default = false */
/*              :interactive-mode          <b_value>, default = false */
/*              :produce-proofs            <b_value>, default = false */
/*              :produce-unsat-cores       <b_value>, default = false */
/*              :produce-models            <b_value>, default = false */
/*              :produce-assignments       <b_value>, default = false */
/*              :regular-output-channel    <string> , default = stdout */
/*              :diagnostic-output-channel <string> , default = stderr */
/*              :random-seed               <numeral>, default = 0 */
/*              :verbosity                 <numeral>, default = 0 */
static name g_parser_print_success             {"smt", "parser", "print-success"};
static name g_parser_expand_definitions        {"smt", "parser", "expand-definitions"};
static name g_parser_interactive_mode          {"smt", "parser", "interactive-mode"};
static name g_parser_produce_proofs            {"smt", "parser", "produce-proofs"};
static name g_parser_produce_unsat_cores       {"smt", "parser", "produce-unsat-cores"};
static name g_parser_produce_models            {"smt", "parser", "produce-models"};
static name g_parser_produce_assignments       {"smt", "parser", "produce-assignments"};
static name g_parser_regular_output_channel    {"smt", "parser", "regular-output-channel"};
static name g_parser_diagnostic_output_channel {"smt", "parser", "diagnostic-output-channel"};
static name g_parser_random_seed               {"smt", "parser", "random-seed"};
static name g_parser_verbosity                 {"smt", "parser", "verbosity"};
RegisterBoolOption(g_parser_print_success              , true ,  "print-success");
RegisterBoolOption(g_parser_expand_definitions         , false,  "expand-definitions");
RegisterBoolOption(g_parser_interactive_mode           , false,  "interactive-mode");
RegisterBoolOption(g_parser_produce_proofs             , false,  "produce-proofs");
RegisterBoolOption(g_parser_produce_unsat_cores        , false,  "produce-unsat-cores");
RegisterBoolOption(g_parser_produce_models             , false,  "produce-models");
RegisterBoolOption(g_parser_produce_assignments        , false,  "produce-assignments");
RegisterStringOption(g_parser_regular_output_channel   , "cout", "regular-output-channel");
RegisterStringOption(g_parser_diagnostic_output_channel, "cerr", "diagnostic-output-channel");
RegisterIntOption(g_parser_random_seed            , 0,      "random-seed");
RegisterIntOption(g_parser_verbosity              , 0,      "verbosity");
bool get_parser_print_success (options const & opts) { return opts.get_bool(g_parser_print_success, SMT_DEFAULT_PARSER_PRINT_SUCCESS); }
bool get_parser_expand_definitions (options const & opts) { return opts.get_bool(g_parser_expand_definitions, SMT_DEFAULT_PARSER_EXPAND_DEFINITIONS); }
bool get_parser_interactive_mode (options const & opts) { return opts.get_bool(g_parser_interactive_mode, SMT_DEFAULT_PARSER_INTERACTIVE_MODE); }
bool get_parser_produce_proofs (options const & opts) { return opts.get_bool(g_parser_produce_proofs, SMT_DEFAULT_PARSER_PRODUCE_PROOFS); }
bool get_parser_produce_unsat_cores (options const & opts) { return opts.get_bool(g_parser_produce_unsat_cores, SMT_DEFAULT_PARSER_PRODUCE_UNSAT_CORES); }
bool get_parser_produce_models (options const & opts) { return opts.get_bool(g_parser_produce_models, SMT_DEFAULT_PARSER_PRODUCE_MODELS); }
bool get_parser_produce_assignments (options const & opts) { return opts.get_bool(g_parser_produce_assignments, SMT_DEFAULT_PARSER_PRODUCE_ASSIGNMENTS); }
std::string get_parser_regular_output_channel (options const & opts) { return opts.get_string(g_parser_regular_output_channel, SMT_DEFAULT_PARSER_REGULAR_OUTPUT_CHANNEL); }
std::string get_parser_diagnostic_output_channel(options const & opts) { return opts.get_string(g_parser_diagnostic_output_channel, SMT_DEFAULT_PARSER_DIAGNOSTIC_OUTPUT_CHANNEL); }
int get_parser_random_seed (options const & opts) { return opts.get_int(g_parser_random_seed, SMT_DEFAULT_PARSER_RANDOM_SEED); }
int get_parser_verbosity (options const & opts) { return opts.get_int(g_parser_verbosity, SMT_DEFAULT_PARSER_VERBOSITY); }

// ==========================================

// ==========================================
// Builtin commands
static name g_set_logic_kwd("set-logic");
static name g_set_option_kwd("set-option");
static name g_set_info_kwd("set-info");
static name g_declare_sort_kwd("declare-sort");
static name g_define_sort_kwd("define-sort");
static name g_declare_fun_kwd("declare-fun");
static name g_define_fun_kwd("define-fun");
static name g_push_kwd("push");
static name g_pop_kwd("pop");
static name g_assert_kwd("assert");
static name g_check_sat_kwd("check-sat");
static name g_get_assertions_kwd("get-assertions");
static name g_get_proof_kwd("get-proof");
static name g_get_unsat_core_kwd("get_unsat-core");
static name g_get_value_kwd("get-value");
static name g_get_assignment_kwd("get-assignment");
static name g_get_option_kwd("get-option");
static name g_get_info_kwd("get-info");
static name g_exit_kwd("exit");

/** \brief Table/List with all builtin command keywords */
static list<name> g_command_keywords = {g_set_logic_kwd, g_set_option_kwd, g_set_info_kwd, g_declare_sort_kwd,
                                        g_define_sort_kwd, g_declare_fun_kwd, g_define_fun_kwd, g_push_kwd,
                                        g_pop_kwd, g_assert_kwd, g_check_sat_kwd, g_get_assertions_kwd,
                                        g_get_proof_kwd, g_get_unsat_core_kwd, g_get_value_kwd, g_get_assignment_kwd,
                                        g_get_option_kwd, g_get_info_kwd, g_exit_kwd};
// ==========================================

// ==========================================

// A name that can't be created by the user.
// It is used as placeholder for parsing A -> B expressions which
// are syntax sugar for (Pi (_ : A), B)
static name g_unused(name(0u), "parser");

/**
    \brief Actual implementation for the parser functional object

    \remark It is an instance of a Pratt parser
    (http://en.wikipedia.org/wiki/Pratt_parser) described in the paper
    "Top down operator precedence". This algorithm is super simple,
    and it is easy to support user-defined infix/prefix/postfix/mixfix
    operators.
*/
class parser::imp {
    typedef scoped_map<name, unsigned, name_hash, name_eq> local_decls;
    typedef std::unordered_map<name, expr, name_hash, name_eq>  builtins;
    typedef std::pair<unsigned, unsigned> pos_info;
    typedef expr_map<pos_info> expr_pos_info;
    frontend       m_frontend;
    scanner        m_scanner;
    elaborator     m_elaborator;
    scanner::token m_curr;
    bool           m_use_exceptions;
    bool           m_interactive;
    bool           m_found_errors;
    local_decls    m_local_decls;
    unsigned       m_num_local_decls;
    context        m_context;
    builtins       m_builtins;
    expr_pos_info  m_expr_pos_info;
    pos_info       m_last_cmd_pos;
    // Reference to temporary parser used to process import command.
    // We need this reference to be able to interrupt it.
    interruptable_ptr<parser>     m_import_parser;
    interruptable_ptr<normalizer> m_normalizer;

    bool           m_show_errors;
    bool           m_print_success;
    bool           m_expand_definitions;
    bool           m_interactive_mode;
    bool           m_produce_proofs;
    bool           m_produce_unsat_cores;
    bool           m_produce_models;
    bool           m_produce_assignments;
    std::string    m_regular_output_channel;
    std::string    m_diagnostic_output_channel;
    int            m_random_seed;
    int            m_verbosity;

    /** \brief Exception used to track parsing erros, it does not leak outside of this class. */
    struct parser_error : public exception {
        pos_info m_pos;
        parser_error(char const * msg, pos_info const & p):exception(msg), m_pos(p) {}
        parser_error(sstream const & msg, pos_info const & p):exception(msg), m_pos(p) {}
    };

    /**
        \brief Auxiliar struct for creating/destroying a new scope for
        local declarations.
    */
    struct mk_scope {
        imp &                 m_fn;
        local_decls::mk_scope m_scope;
        unsigned              m_old_num_local_decls;
        context               m_old_context;
        mk_scope(imp & fn):
            m_fn(fn),
            m_scope(fn.m_local_decls),
            m_old_num_local_decls(fn.m_num_local_decls),
            m_old_context(fn.m_context) {
        }
        ~mk_scope() {
            m_fn.m_num_local_decls = m_old_num_local_decls;
            m_fn.m_context = m_old_context;
        }
    };

    /** \brief Return the current position information */
    pos_info pos() const { return mk_pair(m_scanner.get_line(), m_scanner.get_pos()); }

    /** \brief Return the position associated with \c e. If there is none, then return \c default_pos. */
    pos_info pos_of(expr const & e, pos_info default_pos) {
        auto it = m_expr_pos_info.find(e);
        if (it == m_expr_pos_info.end())
            return default_pos;
        else
            return it->second;
    }

    /** \brief Associate position \c p with \c e and return \c e */
    expr save(expr const & e, pos_info p) { m_expr_pos_info[e] = p; return e; }

    /** \brief Read the next token. */
    void scan() { m_curr = m_scanner.scan(); }
    /** \brief Return the current token */
    scanner::token curr() const { return m_curr; }
    /** \brief Read the next token if the current one is not End-of-file. */
    void next() { if (m_curr != scanner::token::Eof) scan(); }

    /** \brief Return the name associated with the current token. */
    name const & curr_name() const { return m_scanner.get_name_val(); }
    /** \brief Return the numeral associated with the current token. */
    mpq const & curr_num() const { return m_scanner.get_num_val(); }
    /** \brief Return the string associated with the current token. */
    std::string const & curr_string() const { return m_scanner.get_str_val(); }

    /**
        \brief Check if the current token is \c t, and move to the
        next one. If the current token is not \c t, it throws a parser error.
    */
    void check_next(scanner::token t, char const * msg) {
        if (curr() == t)
            next();
        else
            throw parser_error(msg, pos());
    }

    // =========================
    // curr_is_<token> functions
    // =========================
    /** \brief Return true iff the current token is a '(' */
    bool curr_is_lparen() const  { return curr() == scanner::token::LeftParen; }
    /** \brief Return true iff the current token is a ')' */
    bool curr_is_rparen() const  { return curr() == scanner::token::RightParen; }
    /** \brief Return true iff the current token is a Keyword' */
    bool curr_is_keyword() const { return curr() == scanner::token::Keyword; }
    /** \brief Return true iff the current token is a Symbol */
    bool curr_is_symbol() const  { return curr() == scanner::token::Symbol; }
    /** \brief Return true iff the current token is a StringVal */
    bool curr_is_string() const  { return curr() == scanner::token::StringVal; }
    /** \brief Return true iff the current token is a NumVal */
    bool curr_is_num() const     { return curr() == scanner::token::NumVal; }
    /** \brief Return true iff the current token is a BinVal */
    bool curr_is_bin() const     { return curr() == scanner::token::BinVal; }
    /** \brief Return true iff the current token is a HexVal */
    bool curr_is_hex() const     { return curr() == scanner::token::HexVal; }
    /** \brief Return true iff the current token is a DecVal */
    bool curr_is_dec() const     { return curr() == scanner::token::DecVal; }

    // =======================
    // check_<token> functions
    // =======================
    /** \brief Throws a parser error if the current token is not a '('. */
    void check_lparen(char const * msg)  { if (!curr_is_lparen()) throw parser_error(msg, pos()); }
    /** \brief Throws a parser error if the current token is not a ')' */
    void check_rparen(char const * msg)  { if (!curr_is_rparen()) throw parser_error(msg, pos()); }
    /** \brief Throws a parser error if the current token is not a Keyword */
    void check_keyword(char const * msg) { if (!curr_is_keyword()) throw parser_error(msg, pos()); }
    /** \brief Throws a parser error if the current token is not a Symbol */
    void check_symbol(char const * msg)  { if (!curr_is_symbol()) throw parser_error(msg, pos()); }
    /** \brief Throws a parser error if the current token is not a StringVal */
    void check_string(char const * msg)  { if (!curr_is_string()) throw parser_error(msg, pos()); }
    /** \brief Throws a parser error if the current token is not a NumVal */
    void check_num(char const * msg)     { if (!curr_is_num()) throw parser_error(msg, pos()); }
    /** \brief Throws a parser error if the current token is not a BinVal */
    void check_bin(char const * msg)     { if (!curr_is_bin()) throw parser_error(msg, pos()); }
    /** \brief Throws a parser error if the current token is not a HexVal */
    void check_hex(char const * msg)     { if (!curr_is_hex()) throw parser_error(msg, pos()); }
    /** \brief Throws a parser error if the current token is not a DecVal */
    void check_dec(char const * msg)     { if (!curr_is_dec()) throw parser_error(msg, pos()); }
    /** \brief Throws a parser error if the current token is not an identifier named \c op. */
    void check_name(name const & op, char const * msg) { if(!curr_is_symbol() || curr_name() != op) throw parser_error(msg, pos()); }

    // ============================
    // check_<token>_next functions
    // ============================
    /** \brief Throws a parser error if the current token is not '('. If it is, move to the next token. */
    void check_lparen_next(char const * msg) { check_next(scanner::token::LeftParen, msg); }
    /** \brief Throws a parser error if the current token is not ')'. If it is, move to the next token. */
    void check_rparen_next(char const * msg) { check_next(scanner::token::RightParen, msg); }
    /** \brief Throws a parser error if the current token is not Keyword . If it is, move to the next token. */
    name check_keyword_next(char const * msg) { check_keyword(msg); name r = curr_name(); next(); return r; }
    /** \brief Throws a parser error if the current token is not Symbol. If it is, move to the next token. */
    name check_symbol_next(char const * msg) { check_symbol(msg); name r = curr_name(); next(); return r; }
    /** \brief Throws a parser error if the current token is not StringVal. If it is, move to the next token. */
    std::string check_string_next(char const * msg) { check_string(msg); std::string r = curr_string(); next(); return r; }
    /** \brief Throws a parser error if the current token is not NumVal. If it is, move to the next token. */
    mpq const & check_num_next(char const * msg) { check_num(msg); mpq const & n = curr_num(); return n; }
    /** \brief Throws a parser error if the current token is not BinVal. If it is, move to the next token. */
    mpq const & check_bin_next(char const * msg) { check_bin(msg); mpq const & n = curr_num(); return n; }
    /** \brief Throws a parser error if the current token is not HexVal. If it is, move to the next token. */
    mpq const & check_hex_next(char const * msg) { check_hex(msg); mpq const & n = curr_num(); return n; }
    /** \brief Throws a parser error if the current token is not DecVal. If it is, move to the next token. */
    mpq const & check_dec_next(char const * msg) { check_dec(msg); mpq const & n = curr_num(); return n; }
    /** \brief Throws a parser error if the current token is not an identifier named \c op. If it is, move to the next token. */
    void check_name_next(name const & op, char const * msg) { check_name(op, msg); next(); }

    /**
       \brief Try to find an object (Definition or Postulate) named \c
       id in the frontend/environment. If there isn't one, then tries
       to check if \c id is a builtin symbol. If it is not throws an error.
    */
    expr get_name_ref(name const & id, pos_info const & p) {
        object const & obj = m_frontend.find_object(id);
        if (obj) {
            object_kind k      = obj.kind();
            if (k == object_kind::Definition || k == object_kind::Postulate)
                return mk_constant(obj.get_name());
            else
                throw parser_error(sstream() << "invalid object reference, object '" << id << "' is not an expression.", p);
        }
        else {
            auto it = m_builtins.find(id);
            if (it != m_builtins.end()) {
                return it->second;
            } else {
                throw parser_error(sstream() << "unknown identifier '" << id << "'", p);
            }
        }
    }

    /** \brief Initialize \c m_builtins table with Lean builtin symbols that do not have notation associated with them. */
    void init_builtins() {
        m_builtins["Bool"]   = Bool;
        m_builtins["true"]   = True;
        m_builtins["false"]  = False;
        m_builtins["Int"]    = Int;
    }

    expr parse_num() {
        auto p = pos();
        expr r = save(mk_int_value(m_scanner.get_num_val().get_numerator()), p);
        next();
        return r;
    }

    expr parse_hex() {
        auto p = pos();
        expr r = save(mk_int_value(m_scanner.get_num_val().get_numerator()), p);
        next();
        return r;
    }

    expr parse_bin() {
        auto p = pos();
        expr r = save(mk_int_value(m_scanner.get_num_val().get_numerator()), p);
        next();
        return r;
    }

    expr parse_dec() {
        //auto p = pos();
        expr r; // = save(mk_float_value(m_scanner.get_num_val()), p);
        /* TODO */
        not_implemented_yet();
        next();
        return r;
    }

    expr parse_string() {
        /* TODO */
        not_implemented_yet();
    }

    [[ noreturn ]] void not_implemented_yet() {
        // TODO
        throw parser_error("not implemented yet", pos());
    }

    expr elaborate(expr const & e) {
        if (has_metavar(e)) {
            // TODO fix
            m_elaborator.display(std::cerr);
            throw parser_error("expression contains metavariables... not implemented yet.", m_last_cmd_pos);
        } else {
            return e;
        }
    }

    /** \brief Register the name \c n as a local declaration. */
    void register_binding(name const & n, expr const & type, expr const & val = expr()) {
        unsigned lvl = m_num_local_decls;
        if (val)
            m_context = extend(m_context, n, expr(), val);
        else
            m_context = extend(m_context, n, type);
        m_local_decls.insert(n, lvl);
        m_num_local_decls++;
        lean_assert(m_local_decls.find(n)->second == lvl);
    }

    expr parse_let() {
        /* <term> ::= ( let ( <var_binding>+ ) <term> ) */
        next();

        // Save scope
        mk_scope scope(*this);
        check_lparen_next("'(' expected in parse_let");

        // Process variable bindings
        buffer<std::tuple<pos_info, name, expr>> bindings;
        do {
            std::tuple<pos_info, name, expr> binding = parse_var_binding();
            register_binding(std::get<1>(binding), expr(), std::get<2>(binding));
            bindings.push_back(binding);
        } while (curr_is_lparen());
        check_rparen_next("')' expected in parse_let");

        // Process term
        expr r = parse_term();
        unsigned i = bindings.size();
        while (i > 0) {
            --i;
            auto p = std::get<0>(bindings[i]);
            r = save(mk_let(std::get<1>(bindings[i]), std::get<2>(bindings[i]), r), p);
        }
        return r;
    }

    expr parse_quantifier(bool is_forall) {
        /* <term> ::= ( forall/exists ( <sorted_var>+ ) <term> ) */
        next();
        mk_scope scope(*this);

        // Process <sorted_var>+
        check_lparen_next("'(' expected in parse_quantifier");
        buffer<std::tuple<pos_info, name, expr>> bindings;
        do {
            std::tuple<pos_info, name, expr> binding = parse_sorted_var();
            register_binding(std::get<1>(binding), expr(), std::get<2>(binding));
            bindings.push_back(binding);
        } while (curr_is_lparen());
        check_rparen_next("')' expected in parse_quantifier");

        // Process <term>
        expr result = parse_term();

        // Construct mk_<quantifier>
        unsigned i = bindings.size();
        while (i > 0) {
            --i;
            pos_info p = std::get<0>(bindings[i]);
            expr lambda = save(mk_lambda(std::get<1>(bindings[i]), std::get<2>(bindings[i]), result), p);
            if (is_forall)
                result = save(mk_forall(std::get<2>(bindings[i]), lambda), p);
            else
                result = save(mk_exists(std::get<2>(bindings[i]), lambda), p);
        }
        return result;
    }


    expr parse_forall() {
        return parse_quantifier(true);
    }

    expr parse_exists() {
        return parse_quantifier(false);
    }

    std::tuple<name, sexpr> parse_attribute() {
        /* <attribute>       ::= <keyword> | <keyword> <attribute_value> */
        /* <attribute_value> ::= <spec_constant> | <symbol> | ( <s_expr>* ) */
        name key = curr_name();
        next();
        sexpr val;

        switch(curr()) {
        case scanner::token::NumVal:
        case scanner::token::HexVal:
        case scanner::token::BinVal:
            val = sexpr(curr_num().get_numerator());
            next();
            break;
        case scanner::token::DecVal:
            val = sexpr(curr_num());
            next();
            break;
        case scanner::token::StringVal:
            val = sexpr(curr_string());
            next();
            break;
        case scanner::token::Symbol: {
            name n = curr_name();
            if(n == "true") {
                val = true;
            } else if (n == "false") {
                val = false;
            } else {
                val = n;
            }
            next();
            break;
        }
        case scanner::token::LeftParen:
            next();
            // TODO: Currently, it's <s_expr>. change to <s_expr>*
            val = parse_sexpr();
            check_rparen_next("')' expected in parse_attribute");
            break;
        default:
            /* nothing */
            break;
        }
        return std::make_tuple(key, val);
    }

    expr parse_id_terms() {
        /* <term> ::= ( <qual_identifier> <term>+ ) */
        /* TODO */
        not_implemented_yet();
    }

    expr parse_id() {
        auto p = pos();
        name id = curr_name();
        next();
        auto it = m_local_decls.find(id);
        if (it != m_local_decls.end()) {
            return save(mk_var(m_num_local_decls - it->second - 1), p);
        } else {
            return save(get_name_ref(id, p), p);
        }
    }

    expr parse_sort() {
        /* <sort> ::= <identifier> | ( <identifier> <sort>+ ) */
        switch(curr()) {
        case scanner::token::Symbol:
            /* <identifier> */
            return parse_id();
        case scanner::token::LeftParen:
        {
            next();
            expr s = parse_id();
            /* process <sort>* */
            do {
                s = mk_app(s, parse_sort());
            } while(curr_is_symbol() || curr_is_lparen());
            check_rparen_next("')' expected in parse_sort()");
            return s;
        }
        default:
            throw parser_error("parse error in parse_sort()", pos());
        }
    }

    expr parse_qual_id() {
        /* <qual_identifier> ::= <identifier> | ( as <identifier> <sort> ) */
        switch(curr()) {
        case scanner::token::Symbol:
            /* <identifier> */
            return parse_id();
        case scanner::token::LeftParen:
        {
            /* ( as <identifier> <sort> ) */
            next();
            check_name_next("as", "'as' is required for a qualified identifier");
            expr id = parse_id();
            expr s = parse_sort();
            check_rparen_next("')' expected in parse_qual_id()");
            /* TODO */
            break;
        }
        default:
            throw parser_error("parse error in parse_sort()", pos());
        }
        /* TODO */
        not_implemented_yet();
    }

    expr parse_lparen() {
        auto p = pos();
        next();

        expr r;
        switch (curr()) {
        case scanner::token::Symbol:
            if(curr_name() == "let") {
                /* ( let ( <var_binding>+ ) <term> ) */
                r = parse_let();
            } else if(curr_name() == "forall") {
                /* ( forall ( <sorted_var>+ ) <term> ) */
                r = parse_forall();
            } else if(curr_name() == "exists") {
                /* ( exists ( <sorted_var>+ ) <term> ) */
                r = parse_exists();
            } else if(curr_name() == "!") {
                /* ( ! <term> <attribute>+ ) */
                std::tuple<name, sexpr> attr = parse_attribute();
                // TODO r = std::get<1>(attr);
            } else {
                /* ( <qual_identifier) (term)+ */
                r = parse_id_terms();
            }
            break;
        case scanner::token::LeftParen:
        case scanner::token::RightParen:
        case scanner::token::Keyword:
        case scanner::token::StringVal:
        case scanner::token::NumVal:
        case scanner::token::BinVal:
        case scanner::token::HexVal:
        case scanner::token::DecVal:
        case scanner::token::Eof:
            throw parser_error("unexpected token in parse_lparen()", pos());
        }
        r = save(r, p);
        check_rparen_next("')' expected in parse_lparen()");
        return r;
    }
    /**
       \brief Auxiliary method used when processing the beginning of an expression.
    */
    expr parse_nud() {
        switch (curr()) {
        case scanner::token::NumVal: return parse_num();
        case scanner::token::BinVal: return parse_bin();
        case scanner::token::HexVal: return parse_hex();
        case scanner::token::DecVal: return parse_dec();
        case scanner::token::StringVal: return parse_string();
        case scanner::token::LeftParen:  return parse_lparen();
        case scanner::token::Symbol: return parse_id();
        default:
            throw parser_error("unexpected token in parse_nud()", pos());
        }
    }

    expr parse_term(unsigned rbp = 0) {
        expr left = parse_nud();
        return left;
    }

    std::tuple<pos_info, name, expr> parse_sorted_var() {
        /* <sorted_var> ::= ( symbol sort ) */
        auto p = pos();
        check_lparen_next("sorted_var: '(' expected");
        name id = check_symbol_next("invalid fun declaration, identifier expected");
        normalizer norm(m_frontend);
        scoped_set_interruptable_ptr<normalizer> set(m_normalizer, &norm);
        expr sort = norm(parse_sort());
        check_rparen_next("sorted_var: ')' expected");
        return std::make_tuple(p, id, sort);
    }

    std::tuple<pos_info, name, expr> parse_var_binding() {
        /* <var_binding> ::= ( <symbol> <term> ) */
        auto p = pos();
        check_lparen_next("var_binding: '(' expected");
        name id = check_symbol_next("identifier expected in parse_var_binding");
        expr term = parse_term();
        check_rparen_next("var_binding: ')' expected");
        return std::make_tuple(p, id, term);
    }

    void parse_assert() {
        /* <command> ::= ( assert <term> ) */
        lean_assert(curr_is_symbol() && curr_name() == g_assert_kwd);
        next();
        name id = name("assert", pos().first);
        expr e = parse_term();
        m_frontend.add_axiom(id, e);
        if (m_verbosity > 0)
            regular(m_frontend) << "  Assumed: " << id << " = " << e << endl;
    }
    void parse_check_sat() {
        /* <command> ::= ( check-sat ) */
        next();
        if (m_verbosity > 0)
            regular(m_frontend) << "  check-sat: " << endl;
        /* TODO: what should we construct for "check-sat" on the
           kernel side? */
    }
    void parse_declare_fun() {
        /* <command> ::= ( declare-fun <symbol> ( <sort>* ) <sort> ) */
        next();
        name id = check_symbol_next("invalid fun declaration, identifier expected");

        check_lparen_next("invalid token in declare-fun, '(' expected");
        buffer<expr> arg_sorts;
        /* process <sorts>* */
        while(curr_is_symbol() || curr_is_lparen()) {
            expr sort = parse_sort();
            arg_sorts.push_back(sort);
        }
        check_rparen_next("invalid token in declare-fun, ')' expected");
        expr ret_sort = parse_sort();

        unsigned n = arg_sorts.size();
        while(n-- > 0) {
            ret_sort = mk_arrow(arg_sorts[n], ret_sort);
        }

        m_frontend.add_var(id, ret_sort);
        if(m_verbosity > 0)
            regular(m_frontend) << " declare_fun " << id << " " << ret_sort << endl;
    }

    expr mk_abstraction(buffer<std::tuple<pos_info, name, expr>> const & bindings, expr const & body) {
        expr result = body;
        unsigned i = bindings.size();
        while (i > 0) {
            --i;
            pos_info p = std::get<0>(bindings[i]);
            result = save(mk_lambda(std::get<1>(bindings[i]), std::get<2>(bindings[i]), result), p);
        }
        return result;
    }

    void parse_define_fun() {
        /* <command> ::= ( define-fun <symbol> ( <sorted_var>* ) <sort> <term> ) */
        next();
        name id = check_symbol_next("invalid fun declaration, identifier expected");


        check_lparen_next("invalid token in declare-fun, '(' expected");
        // Save scope
        mk_scope scope(*this);
        buffer<std::tuple<pos_info, name, expr>> sorted_vars;
        /* process <sorted_var>* */
        while(curr_is_lparen()) {
            std::tuple<pos_info, name, expr> binding = parse_sorted_var();
            sorted_vars.push_back(binding);
            register_binding(std::get<1>(binding), std::get<2>(binding));
        }
        check_rparen_next("invalid token in declare-fun, ')' expected");
        expr ret_sort = parse_sort();
        expr body = parse_term();

        unsigned i = sorted_vars.size();
        while(i-- > 0) {
            ret_sort = mk_arrow(std::get<2>(sorted_vars[i]), ret_sort);
        }

        expr abs = mk_abstraction(sorted_vars, body);

        m_frontend.add_definition(id, ret_sort, abs);
        if(m_verbosity > 0)
            regular(m_frontend) << " define-fun "
                                << id << " : " << ret_sort
                                << " = "<< abs << endl;
    }
    void parse_declare_sort() {
        /* <command> ::= ( declare-sort <symbol> <numeral> ) */
        next();
        name id = check_symbol_next("invalid sort declaration, identifier expected");
        expr type = Type();
        mpz n = int_value_numeral(parse_num());
        while(n-- > 0) {
            type = mk_arrow(Type(), type);
        }
        m_frontend.add_var(id, type);
        if(m_verbosity > 0)
            regular(m_frontend) << " declare-sort " << id << " : " << type << endl;
    }
    void parse_define_sort() {
        /* <command> ::= ( define-sort <symbol> ( <symbol> *) <sort> ) */
        next();
        name id = check_symbol_next("invalid sort declaration, identifier expected");
        check_lparen_next("invalid token in define-sort, '(' expected");

        buffer<std::tuple<pos_info, name, expr>> args;
        /* process <symbols>* */
        mk_scope scope(*this);
        while(curr_is_symbol()) {
            auto p = pos();
            name arg_name = check_symbol_next("invalid sort declaration, identifier expected");
            args.push_back(std::make_tuple(p, arg_name, Type()));
            register_binding(arg_name, Type());
        }
        check_rparen_next("invalid token in define-sort, ')' expected");

        /* process <sort> */
        expr s = Type();
        unsigned i = args.size();
        while(i-- > 0) {
            s = mk_arrow(Type(), s);
        }

        if(m_verbosity > 0)
            regular(m_frontend) << " define-sort "
                                << id << " : " << s;

        expr body = parse_sort();

        expr abs = mk_abstraction(args, body);
        if(m_verbosity > 0)
            regular(m_frontend) << " = "<< abs << endl;

        m_frontend.add_definition(id, s, abs);

    }
    void parse_exit() {
        /* <command> ::= ( exit ) */
        next();
        /* Nothing */
        /* TODO: what should we construct for this? */
    }
    void parse_get_assertions() {
        /* <command> ::= ( get-assertions ) */
        next();
        /* TODO */
    }
    void parse_get_assignment() {
        /* <command> ::= ( get-assignment ) */
        next();
        /* TODO */
    }

    name parse_info_flag() {
        /* <info_flag> ::= :error-behavior
                           :name
                           :authors
                           :version
                           :status
                           :reason-unknown
                           ⟨keyword⟩
                           :all-statistics */
        return parse_keyword();
    }

    void parse_get_info() {
        /* <command> ::= ( get-info <info_flag> ) */
        next();
        parse_info_flag();
        /* TODO */
    }
    void parse_get_option() {
        /* <command> ::= ( get-option <keyword> ) */
        next();
        std::string key = parse_keyword().to_string();
        name n = {"smt", "parser", key.c_str()};
        auto decl_it = get_option_declarations().find(n);
        lean_assert(decl_it != get_option_declarations().end());
        option_kind k = decl_it->second.kind();

        const options & opt = m_frontend.get_state().get_options();

        if(n == g_parser_print_success) { regular(m_frontend) << get_parser_print_success(opt) << endl; return; }
        if(n == g_parser_expand_definitions ) { regular(m_frontend) << get_parser_expand_definitions(opt) << endl; return; }
        if(n == g_parser_interactive_mode ) { regular(m_frontend) << get_parser_interactive_mode(opt) << endl; return; }
        if(n == g_parser_produce_proofs ) { regular(m_frontend) << get_parser_produce_proofs(opt) << endl; return; }
        if(n == g_parser_produce_unsat_cores ) { regular(m_frontend) << get_parser_produce_unsat_cores(opt) << endl; return; }
        if(n == g_parser_produce_models ) { regular(m_frontend) << get_parser_produce_models(opt) << endl; return; }
        if(n == g_parser_produce_assignments ) { regular(m_frontend) << get_parser_produce_assignments(opt) << endl; return; }
        if(n == g_parser_regular_output_channel ) { regular(m_frontend) << get_parser_regular_output_channel(opt) << endl; return; }
        if(n == g_parser_diagnostic_output_channel ) { regular(m_frontend) << get_parser_diagnostic_output_channel(opt) << endl; return; }
        if(n == g_parser_random_seed ) { regular(m_frontend) << get_parser_random_seed(opt) << endl; return; }
        if(n == g_parser_verbosity ) { regular(m_frontend) << get_parser_verbosity(opt) << endl; return; }

        switch(k) {
        case BoolOption:
            regular(m_frontend) << m_frontend.get_state().get_options().get_bool(n)
                                << endl;
            return;
        case IntOption:
            regular(m_frontend) << m_frontend.get_state().get_options().get_int(n)
                                << endl;
            return;
        case UnsignedOption:
            regular(m_frontend) << m_frontend.get_state().get_options().get_unsigned(n)
                                << endl;
            return;
            break;
        case DoubleOption:
            regular(m_frontend) << m_frontend.get_state().get_options().get_double(n)
                                << endl;
            return;
        case StringOption:
            regular(m_frontend) << m_frontend.get_state().get_options().get_string(n)
                                << endl;
            return;
        case SExprOption:
            regular(m_frontend) << m_frontend.get_state().get_options().get_sexpr(n)
                                << endl;
            return;
        }
    }

    void parse_get_proof() {
        /* <command> ::= ( get-proof ) */
        next();
        /* TODO */
    }
    void parse_get_unsat_core() {
        /* <command> ::= ( get-unsat-core ) */
        next();
        /* TODO */
    }
    void parse_get_value() {
        /* <command> ::= ( get-value ( <term> + ) ) */
        next();
        check_lparen_next("'(' expected in parse_get_value()");
        /* TODO: process <term>+ */
        expr term = parse_term();
        check_rparen_next("')' expected in parse_get_value()");
        /* TODO */
    }
    void parse_pop() {
        /* <command> ::= ( pop <numeral> ) */
        next();
        mpz n = int_value_numeral(parse_num());
        lean_assert(n >= 0);
        while(n-- > 0) {
            lean_assert(m_frontend.has_parent());
            m_frontend = m_frontend.parent();
            if(m_verbosity > 0)
                regular(m_frontend) << " (pop) " << endl;
        }
    }
    void parse_push() {
        next();
        mpz n = int_value_numeral(parse_num());
        lean_assert(n >= 0);
        while(n-- > 0) {
            m_frontend = m_frontend.mk_child();
            if(m_verbosity > 0)
                regular(m_frontend) << " (push) " << endl;
        }
    }
    void parse_set_info() {
        /* <command> ::= ( set-info <attribute> ) */
        next();
        std::tuple<name, sexpr> attr = parse_attribute();
        /* TODO */
    }

    void parse_set_logic() {
        next();
        name logic = check_symbol_next("logic symbol is expected.");
        /* TODO */
    }

    name parse_keyword() {
        name n = curr_name();
        next();
        return n;
    }

    expr parse_spec_constant() {
        /* <spec_constant> ::= <numeral> | <decimal> | <hexadecimal> | <binary> | <string>  */
        switch(curr()) {
        case scanner::token::NumVal:
            return parse_num();
        case scanner::token::DecVal:
            return parse_dec();
        case scanner::token::HexVal:
            return parse_hex();
        case scanner::token::BinVal:
            return parse_bin();
        case scanner::token::StringVal:
            return parse_string();
        default:
            throw parser_error("parse error in parse_spec_constant", pos());
        }
    }

    expr parse_sexpr() {
        /* <s_expr> ::= <spec_constant> | <symbol> | <keyword> | ( <s_expr>* ) */
        switch(curr()) {
        case scanner::token::NumVal:
        case scanner::token::DecVal:
        case scanner::token::HexVal:
        case scanner::token::BinVal:
        case scanner::token::StringVal:
            return parse_spec_constant();
        case scanner::token::Symbol:
            return parse_id();
        case scanner::token::Keyword:
            return parse_id(); /* TODO: what's the meaning of keyword in sexpression? */
        case scanner::token::LeftParen: {
            next();
            expr t = parse_sexpr();
            check_rparen_next("')' expected in parse_sexpr");
            return t;
        }
        default:
            throw parser_error("parse error in parse_sexpr()", pos());
        }
    }

    std::tuple<name, sexpr> parse_option() {
        /* <option> ::= :print-success             <b_value>, default = true */
        /*              :expand-definitions        <b_value>, default = false */
        /*              :interactive-mode          <b_value>, default = false */
        /*              :produce-proofs            <b_value>, default = false */
        /*              :produce-unsat-cores       <b_value>, default = false */
        /*              :produce-models            <b_value>, default = false */
        /*              :produce-assignments       <b_value>, default = false */
        /*              :regular-output-channel    <string> , default = stdout */
        /*              :diagnostic-output-channel <string> , default = stderr */
        /*              :random-seed               <numeral>, default = 0 */
        /*              :verbosity                 <numeral>, default = 0 */
        /*              <attribute>                          */
        /* TODO */
        return parse_attribute();
    }

    option_kind extract_option_kind(sexpr & e) {
        switch(e.kind()) {
        case sexpr_kind::NIL:
        case sexpr_kind::CONS:
            return SExprOption;
        case sexpr_kind::STRING:
            return StringOption;
        case sexpr_kind::BOOL:
            return BoolOption;
        case sexpr_kind::INT:
            return IntOption;
        case sexpr_kind::DOUBLE:
            return DoubleOption;
        case sexpr_kind::NAME:
            /* TODO */
            return StringOption;
        case sexpr_kind::MPZ:
            /* TODO */
            return IntOption;
        case sexpr_kind::MPQ:
            /* TODO */
            return DoubleOption;
        }
    }

    void parse_set_option() {
        next();
        std::tuple<name, sexpr> opt = parse_option();
        std::string key = std::get<0>(opt).to_string();
        name n = name({"smt", "parser", key.c_str()});
        sexpr e = std::get<1>(opt);
        option_kind k = extract_option_kind(e);

        auto decl_it = get_option_declarations().find(n);
        if(decl_it == get_option_declarations().end()) {
            // option is not registered
            mk_option_declaration(n, k, "false", "");
        } else {
            // option is registered. check out its kind
            option_kind saved_kind = decl_it->second.kind();
            lean_assert(k == saved_kind);
        }
        switch(k) {
        case BoolOption:
            m_frontend.set_option(n, e.get_bool());
            break;
        case IntOption:
            m_frontend.set_option(n, e.get_int());
            break;
        case UnsignedOption:
            m_frontend.set_option(n, e.get_int());
            break;
        case DoubleOption:
            m_frontend.set_option(n, e.get_double());
            break;
        case StringOption:
            m_frontend.set_option(n, e.get_string());
            break;
        case SExprOption:
            m_frontend.set_option(n, e);
            break;
        }
    }

    /** \brief Parse a Lean command. */
    void parse_command() {
        lean_assert(curr_is_lparen());
        next();
        check_symbol("invalid command, symbol expected");

        name const & cmd_id = curr_name();
        if      (cmd_id == g_assert_kwd        ) parse_assert();
        else if (cmd_id == g_check_sat_kwd     ) parse_check_sat();
        else if (cmd_id == g_declare_fun_kwd   ) parse_declare_fun();
        else if (cmd_id == g_declare_sort_kwd  ) parse_declare_sort();
        else if (cmd_id == g_define_fun_kwd    ) parse_define_fun();
        else if (cmd_id == g_define_sort_kwd   ) parse_define_sort();
        else if (cmd_id == g_exit_kwd          ) parse_exit();
        else if (cmd_id == g_get_assertions_kwd) parse_get_assertions();
        else if (cmd_id == g_get_assignment_kwd) parse_get_assignment();
        else if (cmd_id == g_get_info_kwd      ) parse_get_info();
        else if (cmd_id == g_get_option_kwd    ) parse_get_option();
        else if (cmd_id == g_get_proof_kwd     ) parse_get_proof();
        else if (cmd_id == g_get_unsat_core_kwd) parse_get_unsat_core();
        else if (cmd_id == g_get_value_kwd     ) parse_get_value();
        else if (cmd_id == g_pop_kwd           ) parse_pop();
        else if (cmd_id == g_push_kwd          ) parse_push();
        else if (cmd_id == g_set_info_kwd      ) parse_set_info();
        else if (cmd_id == g_set_logic_kwd     ) parse_set_logic();
        else if (cmd_id == g_set_option_kwd    ) parse_set_option();
        else { next(); throw parser_error(sstream() << "invalid command '" << cmd_id << "'", m_last_cmd_pos); }

        check_rparen_next("invalid command, ')' expected");
    }

    void display_error_pos(unsigned line, unsigned pos) { regular(m_frontend) << "Error (line: " << line << ", pos: " << pos << ")"; }
    void display_error_pos(pos_info const & p) { display_error_pos(p.first, p.second); }
    void display_error_pos(expr const & e) {
        if (e) {
            auto it = m_expr_pos_info.find(e);
            if (it == m_expr_pos_info.end())
                return display_error_pos(m_last_cmd_pos);
            else
                return display_error_pos(it->second);
        } else {
            return display_error_pos(m_last_cmd_pos);
        }
    }
    void display_error(char const * msg, unsigned line, unsigned pos) {
        display_error_pos(line, pos);
        regular(m_frontend) << " " << msg << endl;
        sync();
    }
    void display_error(char const * msg) {
        display_error(msg, m_scanner.get_line(), m_scanner.get_pos());
    }
    void display_error(kernel_exception const & ex) {
        display_error_pos(ex.get_main_expr());
        regular(m_frontend) << " " << ex << endl;
        sync();
    }

    void updt_options() {
        // m_print_success             = get_parser_print_success (m_frontend.get_state().get_options());
        // m_expand_definitions        = get_parser_expand_definitions (m_frontend.get_state().get_options());
        // m_interactive_mode          = get_parser_interactive_mode (m_frontend.get_state().get_options());
        // m_produce_proofs            = get_parser_produce_proofs (m_frontend.get_state().get_options());
        // m_produce_unsat_cores       = get_parser_produce_unsat_cores (m_frontend.get_state().get_options());
        // m_produce_models            = get_parser_produce_models (m_frontend.get_state().get_options());
        // m_produce_assignments       = get_parser_produce_assignments (m_frontend.get_state().get_options());
        // m_regular_output_channel    = get_parser_regular_output_channel (m_frontend.get_state().get_options());
        // m_diagnostic_output_channel = get_parser_diagnostic_output_channel(m_frontend.get_state().get_options());
        // m_random_seed               = get_parser_random_seed (m_frontend.get_state().get_options());
        // m_verbosity                 = get_parser_verbosity (m_frontend.get_state().get_options());
    }

    /** \brief Keep consuming tokens until we find a Command or End-of-file. */
    void sync() {
        show_prompt();
        while (curr() != scanner::token::Symbol && curr() != scanner::token::Eof)
            next();
    }

public:
    imp(frontend & fe, std::istream & in, bool use_exceptions, bool interactive):
        m_frontend(fe),
        m_scanner(in),
        m_elaborator(fe),
        m_use_exceptions(use_exceptions),
        m_interactive(interactive) {
        updt_options();
        m_found_errors = false;
        m_num_local_decls = 0;
//        m_scanner.set_command_keywords(g_command_keywords);
        init_builtins();
        scan();
    }

    static void show_prompt(bool interactive, frontend const & fe) {
        if (interactive) {
            regular(fe) << "# ";
            regular(fe).flush();
        }
    }

    void show_prompt() {
        show_prompt(m_interactive, m_frontend);
    }

    /** \brief Parse a sequence of commands. This method also perform error management. */
    bool parse_commands() {
        while (true) {
            try {
                switch (curr()) {
                case scanner::token::LeftParen: parse_command(); break;
//                case scanner::token::Period: show_prompt(); next(); break;
                case scanner::token::Eof: return !m_found_errors;
                default:
                    std::cerr << "Error in Parse_command: |" << curr() << " " << std::endl;
                    next();
                    throw parser_error("Command expected", pos());
                }
            } catch (parser_error & ex) {
                m_found_errors = true;
                if (m_show_errors)
                    display_error(ex.what(), ex.m_pos.first, ex.m_pos.second);
                if (m_use_exceptions) {
                    throw parser_exception(ex.what(), ex.m_pos.first, ex.m_pos.second);
                }
            } catch (kernel_exception & ex) {
                m_found_errors = true;
                if (m_show_errors)
                    display_error(ex);
                if (m_use_exceptions)
                    throw;
            } catch (interrupted & ex) {
                if (m_verbosity > 0)
                    regular(m_frontend) << "\n!!!Interrupted!!!" << endl;
                sync();
                if (m_use_exceptions)
                    throw;
            } catch (exception & ex) {
                m_found_errors = true;
                if (m_show_errors)
                    display_error(ex.what());
                if (m_use_exceptions)
                    throw;
            }
        }
    }

    // /** \brief Parse an expression. */
    // expr parse_expr_main() {
    //     try {
    //         return elaborate(parse_expr());
    //     } catch (parser_error & ex) {
    //         throw parser_exception(ex.what(), ex.m_pos.first, ex.m_pos.second);
    //     }
    // }

    void set_interrupt(bool flag) {
        m_frontend.set_interrupt(flag);
        m_elaborator.set_interrupt(flag);
        m_import_parser.set_interrupt(flag);
        m_normalizer.set_interrupt(flag);
    }

    void reset_interrupt() {
        set_interrupt(false);
    }
};

parser::parser(frontend fe, std::istream & in, bool use_exceptions, bool interactive) {
    parser::imp::show_prompt(interactive, fe);
    m_ptr.reset(new imp(fe, in, use_exceptions, interactive));
}

parser::~parser() {
}

bool parser::operator()() {
    return m_ptr->parse_commands();
}

void parser::set_interrupt(bool flag) {
    m_ptr->set_interrupt(flag);
}

// expr parser::parse_expr() {
//     return m_ptr->parse_expr_main();
// }

shell::shell(frontend & fe):m_frontend(fe) {
}

shell::~shell() {
}

bool shell::operator()() {
#ifdef LEAN_USE_READLINE
    bool errors = false;
    char * input;
    while (true) {
        input = readline("# ");
        if (!input)
            return errors;
        add_history(input);
        std::istringstream strm(input);
        {
            parser p(m_frontend, strm, false, false);
            scoped_set_interruptable_ptr<parser> set(m_parser, &p);
            if (!p())
                errors = true;
        }
        free(input);
    }
#else
    parser p(m_frontend, std::cin, false, true);
    scoped_set_interruptable_ptr<parser> set(m_parser, &p);
    return p();
#endif
}

void shell::set_interrupt(bool flag) {
    m_parser.set_interrupt(flag);
}
}
}
