/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
        Leonardo de Moura
*/
#include <cstdio>
#include <string>
#include <algorithm>
#include "smt_scanner.h"
#include "trace.h"
#include "debug.h"
#include "exception.h"

namespace lean {
namespace smt {
static name g_lambda_name("fun");
static name g_type_name("Type");
static name g_pi_name("Pi");
static name g_let_name("let");
static name g_arrow_name("->");
static name g_eq_name("=");
static name g_forall_name("forall");
static name g_exists_name("exists");

static name g_par_name("par");
static name g_numeral_name("NUMERAL");
static name g_decimal_name("DECIMAL");
static name g_string_name("STRING");
static name g_as_name("as");

static char g_normalized[256];

/** \brief Auxiliary class for initializing global variable \c g_normalized. */
class init_normalized_table {
    void set(int i, char v) { g_normalized[static_cast<unsigned>(i)] = v; }
public:
    init_normalized_table() {
        // by default all characters are in group c,
        for (int i = 0; i <= 255; i++)
            set(i, 'c');

        // digits normalize to '0'
        for (int i = '0'; i <= '9'; i++)
            set(i, '0');

        // characters that can be used to create ids of group a
        for (int i = 'a'; i <= 'z'; i++)
            set(i, 'a');
        for (int i = 'A'; i <= 'Z'; i++)
            set(i, 'a');

        // SMT2 "Symbols": ~ ! @ $ % ^ & * _ - + = < > . ? /
        for (unsigned char a : {'~', '!', '@', '$', '%', '^', '&', '*', '_', '-', '+', '=', '<', '>', '.', '?'})
            set(a, 'a');
        set('-', '-');        // treat '-' specially

        // spaces
        set(' ',  ' ');
        set('\t', ' ');
        set('\r', ' ');

        // new line
        set('\n', '\n');

        set('#', '#');
        set('"', '"');
        set(';', ';');
        set('(', '(');
        set(')', ')');
        set(':', ':');
        set('|', '|');

        // eof
        set(255, -1);
    }
};

static init_normalized_table g_init_normalized_table;

char normalize(char c) {
    return g_normalized[static_cast<unsigned char>(c)];
}

scanner::scanner(std::istream& stream):
    m_spos(0),
    m_curr(0),
    m_line(1),
    m_pos(0),
    m_stream(stream) {
    next();
}

scanner::~scanner() {
}

void scanner::throw_exception(char const * msg) {
    throw parser_exception(msg, m_line, m_spos);
}

void scanner::next() {
    lean_assert(m_curr != EOF);
    m_curr = m_stream.get();
    m_spos++;
}

bool scanner::check_next(char c) {
    lean_assert(m_curr != EOF);
    bool r = m_stream.get() == c;
    m_stream.unget();
    return r;
}

void scanner::read_comment() {
    lean_assert(curr() == ';');
    next();
    while (true) {
        char c = curr();
        if(c == EOF) {
            return;
        }
        if(c == '\n') {
            new_line();
            next();
            return;
        }
        next();
    }
}

scanner::token scanner::read_quoted_symbol() {
    lean_assert(curr() == '|');
    bool escape = false;
    m_buffer.clear();
    next();
    while (true) {
        char c = curr();
        if (c == EOF) {
            throw_exception("unexpected end of quoted symbol");
        }
        else if (c == '\n') {
            new_line();
        }
        else if (c == '|' && !escape) {
            next();
            m_name_val = name(m_buffer.c_str());
            lean_trace("scanner", tout << "new quoted symbol: " << m_name_val << "\n";);
            return token::Symbol;
        }
        escape = (c == '\\');
        m_buffer += c;
        next();
    }
}

scanner::token scanner::read_symbol_core() {
    while (true) {
        char c = curr();
        char n = normalize(c);
        if (n == 'a' || n == '0' || n == '-') {
            m_buffer += c;
            next();
        }
        else {
            m_name_val = name(m_buffer.c_str());
            lean_trace("scanner", tout << "new symbol: " << m_name_val << "\n";);
            return token::Symbol;
        }
    }
}

scanner::token scanner::read_symbol() {
    lean_assert(normalize(curr()) == 'a' || curr() == ':' || curr() == '-');
    m_buffer.clear();
    m_buffer += curr();
    next();
    return read_symbol_core();
}

bool is_digit_2(const char c) {
    return ('0' == c || c <= '1');
}

bool is_digit_16(const char c) {
    return (('0' <= c && c <= '9') ||
            ('a' <= c && c <= 'f') ||
            ('A' <= c && c <= 'F'));
}

template<typename F>
scanner::token scanner::read_number_radix(unsigned int radix, F check, scanner::token ret) {
    static_assert(std::is_same<F, bool(*)(char)>::value,
                  "smt::scanner::read_number_radix() is called with a wrong check function.");
    lean_assert(check(curr()));
    m_buffer.clear();
    m_buffer += curr();
    next();
    while (true) {
        char c = curr();
        if (check(c)) {
            m_buffer += curr();
            next();
        } else {
            break;
        }
    }
    m_num_val = mpq(m_buffer, radix);
    return ret;
}

scanner::token scanner::read_number() {
    lean_assert('0' <= curr() && curr() <= '9');
    mpq q(1);
    m_num_val = curr() - '0';
    next();
    bool is_decimal = false;

    while (true) {
        char c = curr();
        if ('0' <= c && c <= '9') {
            m_num_val = 10*m_num_val + (c - '0');
            if (is_decimal)
                q *= 10;
            next();
        } else if (c == '.') {
            if (is_decimal)
                break;
            is_decimal = true;
            next();
        } else {
            break;
        }
    }
    if (is_decimal)
        m_num_val /= q;
    return is_decimal ? token::DecVal : token::NumVal;
}

scanner::token scanner::read_string() {
    lean_assert(curr() == '\"');
    next();
    m_buffer.clear();
    while (true) {
        char c = curr();
        if (c == EOF) {
            throw_exception("unexpected end of string");
        } else if (c == '\"') {
            next();
            return token::StringVal;
        } else if (c == '\n') {
            new_line();
        } else if (c == '\\') {
            next();
            c = curr();
            if (c == EOF)
                throw_exception("unexpected end of string");
            if (c != '\\' && c != '\"' && c != 'n')
                throw_exception("invalid escape sequence");
            if (c == 'n')
                c = '\n';
        }
        m_buffer += c;
        next();
    }
}

scanner::token scanner::scan() {
    while (true) {
        char c = curr();
        m_pos = m_spos;
        switch (normalize(c)) {
        case ' ':  next(); break;
        case '\n': next(); new_line(); break;
        case ';':  read_comment(); break;
        case ':':  read_symbol(); return token::Keyword;
        case '(':  next(); return token::LeftParen;
        case ')':  next(); return token::RightParen;
        case '|':  return read_quoted_symbol();
        case 'a':  return read_symbol();
        case '"':  return read_string();
        case '0':  return read_number();
        case '#':
            next();
            if(curr() == 'b') {
                next();
                return read_number_radix(2, is_digit_2, token::BinVal);
            }
            else if(curr() == 'x') {
                next();
                return read_number_radix(16, is_digit_16, token::HexVal);
            }
            lean_unreachable();
            break;
        case '-':
            return read_symbol();
            /* TODO */
            // Treat this as a beginning of signed number (optional)
            // return read_signed_number();
        case -1:   return token::Eof;
        default:   std::cerr << "Invalid Token: " << c << " " << normalize(c) << std::endl; lean_unreachable();
        }
    }
}

std::ostream & operator<<(std::ostream & out, scanner::token const & t) {
    switch (t) {
    case scanner::token::LeftParen:         out << "("; break;
    case scanner::token::RightParen:        out << ")"; break;
    case scanner::token::Keyword:           out << "Keyword"; break;
    case scanner::token::Symbol:            out << "Symbol"; break;
    case scanner::token::StringVal:         out << "StringVal"; break;
    case scanner::token::NumVal:            out << "NumVal"; break;
    case scanner::token::BinVal:            out << "BinVal"; break;
    case scanner::token::HexVal:            out << "HexVal"; break;
    case scanner::token::DecVal:            out << "DecVal"; break;
    case scanner::token::Eof:               out << "EOF"; break;
    }
    return out;
}
}
}
