/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
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
#include "smt_frontend.h"
#include "smt_parser.h"
#include "smt_scanner.h"
#include "smt_notation.h"
#include "smt_pp.h"
#ifdef SMT_USE_READLINE
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <readline/readline.h>
#include <readline/history.h>
#endif

namespace lean {
namespace smt {
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
// Auxiliary constant used to mark applications of overloaded operators.
static name g_overload_name(name(name(name(0u), "parser"), "overload"));
static expr g_overload = mk_constant(g_overload_name);
// ==========================================

// A name that can't be created by the user.
// It is used as placeholder for parsing A -> B expressions which
// are syntax sugar for (Pi (_ : A), B)
static name g_unused(name(0u), "parser");

/**
    \brief Functional object for parsing

    \remark It is an instance of a Pratt parser
    (http://en.wikipedia.org/wiki/Pratt_parser) described in the paper
    "Top down operator precedence". This algorithm is super simple,
    and it is easy to support user-defined infix/prefix/postfix/mixfix
    operators.
*/
class parser_fn {
    typedef scoped_map<name, unsigned, name_hash, name_eq> local_decls;
    typedef std::unordered_map<name, expr, name_hash, name_eq>  builtins;
    typedef std::pair<unsigned, unsigned> pos_info;
    typedef expr_map<pos_info> expr_pos_info;

    frontend       m_frontend;
    scanner        m_scanner;
    scanner::token m_curr;
    bool           m_use_exceptions;
//    bool           m_interactive;
    bool           m_found_errors;
    local_decls    m_local_decls;
    unsigned       m_num_local_decls;
    builtins       m_builtins;
    expr_pos_info  m_expr_pos_info;
    pos_info       m_last_cmd_pos;


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
        parser_fn &           m_fn;
        local_decls::mk_scope m_scope;
        unsigned              m_old_num_local_decls;
        mk_scope(parser_fn & fn):m_fn(fn), m_scope(fn.m_local_decls), m_old_num_local_decls(fn.m_num_local_decls) {}
        ~mk_scope() { m_fn.m_num_local_decls = m_old_num_local_decls; }
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
    /** \brief Keep consume tokens until we find a Command or End-of-file. */
    void sync() {
        while (curr() != scanner::token::Symbol && curr() != scanner::token::Eof)
            next();
    }

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

    /** \brief Initialize \c m_builtins table with Lean builtin symbols that do not have notation associated with them. */
    void init_builtins() {
        m_builtins["Bool"]   = Bool;
        m_builtins["true"]   = True;
        m_builtins["false"]  = False;
        m_builtins["Int"]    = Int;
        /* Real, List, Set, BitVec, FixedSizeList */
    }

    [[ noreturn ]] void not_implemented_yet() {
        // TODO
        throw parser_error("not implemented yet", pos());
    }

    /**
       @name Parse Expressions
    */
    /*@{*/

    /**
       \brief Return the function associated with the given operator.
       If the operator has been overloaded, it returns an expression
       of the form (overload f_k ... (overload f_2 f_1) ...)
       where f_i's are different options.
       After we finish parsing, the procedure #elaborate will
       resolve/decide which f_i should be used.
    */
    expr mk_fun(operator_info const & op) {
        list<expr> const & fs = op.get_exprs();
        lean_assert(!is_nil(fs));
        auto it = fs.begin();
        expr r = *it;
        ++it;
        for (; it != fs.end(); ++it)
            r = mk_app(g_overload, *it, r);
        return r;
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

    expr elaborate(expr const & e) {
        // TODO
        return e;
    }

    expr parse_expr() {
        switch(curr()) {
        case scanner::token::NumVal: return parse_num();
        case scanner::token::BinVal: return parse_bin();
        case scanner::token::HexVal: return parse_hex();
        case scanner::token::DecVal: return parse_dec();
        case scanner::token::StringVal: return parse_string();
        case scanner::token::Symbol:
            /* TODO */
            not_implemented_yet();
            break;

        case scanner::token::LeftParen:
        {
            /* TODO */
            /* ( as <identifier> <sort> ) */
            /* ( <qual_identifier) (term)+ */
            /* ( let ( <var_binding>+ ) <term> ) */
            /* ( forall ( <sorted_var>+ ) <term> ) */
            /* ( exists ( <sorted_var>+ ) <term> ) */
            /* ( ! <term> <attribute>+ ) */
            not_implemented_yet();
            break;
        }
        case scanner::token::Keyword:
        case scanner::token::RightParen:
        case scanner::token::Eof:
            throw parser_error("invalid expression, unexpected token", pos());
        }
        lean_unreachable();
    }

    void parse_assert() {
        /* (assert) */
        lean_assert(curr_is_symbol() && curr_name() == g_assert_kwd);
        next();
        expr v = elaborate(parse_expr());
        expr t = infer_type(v, m_frontend);
        /* TODO : Check t = bool */
        regular(m_frontend) << t << endl;
    }
    void parse_check_sat() {
        /* (check-sat) */
        /* TODO: what should we construct for "check-sat" on the
           kernel side? */
    }
    void parse_declare_fun() {
        /* TODO */
        /* declare-fun <symbol> ( <sort>* ) <sort>  */
    }
    void parse_define_fun() {
        /* TODO */
        /* define-fun <symbol> ( <sorted_var>* ) <sort> <term>  */
    }
    void parse_declare_sort() {
        /* TODO */
        /* declare-sort <symbol> <numeral> */
    }
    void parse_define_sort() {
        /* TODO */
        /* define-sort <symbol> ( <symbol> *) <sort>  */
    }
    void parse_exit() {
        /* Nothing */
        /* TODO: what should we construct for this? */
    }
    void parse_get_assertions_kwd() {
        /* TODO: X */
    }
    void parse_get_assignment_kwd() {
        /* TODO: X */
    }
    void parse_get_info() {
        /* TODO: X */
    }
    void parse_get_option() {
        /* TODO */
    }
    void parse_get_proof() {
        /* TODO */
    }
    void parse_get_unsat_core_kwd() {
        /* TODO */
    }
    void parse_get_value() {
        /* TODO */
    }
    void parse_pop() {
        /* TODO */
    }
    void parse_push() {
        /* TODO */
    }
    void parse_set_info() {
        /* TODO */
    }
    void parse_set_logic() {
        /* TODO */
    }
    void parse_set_option() {
        /* TODO */
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
        else if (cmd_id == g_get_assertions_kwd) parse_get_assertions_kwd();
        else if (cmd_id == g_get_assignment_kwd) parse_get_assignment_kwd();
        else if (cmd_id == g_get_info_kwd      ) parse_get_info();
        else if (cmd_id == g_get_option_kwd    ) parse_get_option();
        else if (cmd_id == g_get_proof_kwd     ) parse_get_proof();
        else if (cmd_id == g_get_unsat_core_kwd) parse_get_unsat_core_kwd();
        else if (cmd_id == g_get_value_kwd     ) parse_get_value();
        else if (cmd_id == g_pop_kwd           ) parse_pop();
        else if (cmd_id == g_push_kwd          ) parse_push();
        else if (cmd_id == g_set_info_kwd      ) parse_set_info();
        else if (cmd_id == g_set_logic_kwd     ) parse_set_logic();
        else if (cmd_id == g_set_option_kwd    ) parse_set_option();
        else { lean_unreachable(); }
    }
    /*@}*/

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

public:
    parser_fn(frontend & fe, std::istream & in, bool use_exceptions):
        m_frontend(fe),
        m_scanner(in),
        m_use_exceptions(use_exceptions) {
        m_found_errors = false;
        m_num_local_decls = 0;
//        m_scanner.set_command_keywords(g_command_keywords);
        init_builtins();
        scan();
    }

    /** \brief Parse a sequence of commands. This method also perform error management. */
    bool parse_commands() {
        while (true) {
            try {
                switch (curr()) {
                case scanner::token::LeftParen: parse_command(); break;
                case scanner::token::Eof: return !m_found_errors;
                default:
                    throw parser_error("Command expected", pos());
                }
            } catch (parser_error & ex) {
                m_found_errors = true;
                if (m_use_exceptions) {
                    throw parser_exception(ex.what(), ex.m_pos.first, ex.m_pos.second);
                } else {
                    display_error(ex.what(), ex.m_pos.first, ex.m_pos.second);
                }
            } catch (kernel_exception & ex) {
                m_found_errors = true;
                if (m_use_exceptions) {
                    throw;
                } else {
                    display_error(ex);
                }
            } catch (interrupted & ex) {
                if (m_use_exceptions) {
                    throw;
                } else {
                    regular(m_frontend) << "\n!!!Interrupted!!!" << endl;
                    sync();
                }
            } catch (exception & ex) {
                m_found_errors = true;
                if (m_use_exceptions) {
                    throw;
                } else {
                    display_error(ex.what());
                }
            }
        }
    }

    // /** \brief Parse an expression. */
    // expr parse_expr_main() {
    //     try {
    //         return elaborate(parse_expr());
    //     } catch (parser_error & ex) {
    //         throw parser_exception(ex.what(), m_scanner.get_line(), m_scanner.get_pos());
    //     }
    // }

};
bool parse_commands(frontend & fe, std::istream & in, bool use_exceptions) {
    return parser_fn(fe, in, use_exceptions).parse_commands();
}

bool parse_commands_from_stdin(frontend & fe) {
#ifdef SMT_USE_READLINE
    bool errors = false;
    char * input;
    while (true) {
        input = readline("# ");
        if (!input)
            return errors;
        add_history(input);
        std::istringstream strm(input);
        if (!parse_commands(fe, strm, false, false))
            errors = true;
        free(input);
    }
#else
    return parse_commands(fe, std::cin, false) ? 0 : 1;
#endif
}

// expr parse_expr(frontend const & fe, std::istream & in) {
//     return parser_fn(const_cast<frontend&>(fe), in, nullptr, nullptr, true).parse_expr_main();
// }
}
}
