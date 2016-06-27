/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/rb_map.h"
#include "util/list_fn.h"
#include "kernel/replace_fn.h"
#include "library/expr_lt.h"
#include "library/idx_metavar.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_list.h"
#include "library/tactic/tactic_state.h"

namespace lean {
/*
structure pattern :=
(target : expr) (output : list expr) (nuvars : nat) (nmvars : nat)
*/
vm_obj mk_pattern(expr const & target, list<expr> const & os, unsigned nuvars, unsigned nmvars) {
    return mk_vm_constructor(0, to_obj(target), to_obj(os), mk_vm_nat(nuvars), mk_vm_nat(nmvars));
}

void get_pattern_fields(vm_obj const & p, expr & target, list<expr> & os, unsigned & nuvars, unsigned & nmvars) {
    lean_assert(csize(p) == 4);
    target = to_expr(cfield(p, 0));
    os     = to_list_expr(cfield(p, 1));
    nuvars = force_to_unsigned(cfield(p, 2), 0);
    nmvars = force_to_unsigned(cfield(p, 3), 0);
}

struct mk_pattern_fn {
    typedef rb_tree<level, level_quick_cmp>        level_set;
    typedef rb_tree<expr, expr_quick_cmp>          expr_set;
    typedef rb_map<level, level, level_quick_cmp> level2meta;
    typedef rb_map<expr, expr, expr_quick_cmp>    expr2meta;
    type_context m_ctx;
    level2meta   m_level2meta;
    expr2meta    m_expr2meta;
    level_set    m_found_levels;
    expr_set     m_found_exprs;

    mk_pattern_fn(tactic_state const & s):
        m_ctx(mk_type_context_for(s)) {
    }

    void mk_level_uvars(list<level> const & ls) {
        unsigned i = 0;
        for (level const & l : ls) {
            m_level2meta.insert(l, mk_idx_metauniv(i));
            i++;
        }
    }

    level convert(level const & l) {
        return replace(l, [&](level const & l) {
                if (auto m = m_level2meta.find(l)) {
                    m_found_levels.insert(l);
                    return some_level(*m);
                }
                return none_level();
            });
    }

    list<level> convert(list<level> const & ls) {
        return map_reuse(ls, [&](level const & l) { return convert(l); });
    }

    expr convert(expr const & e) {
        return replace(e, [&](expr const & e, unsigned) {
                if (auto m = m_expr2meta.find(e)) {
                    m_found_exprs.insert(e);
                    return some_expr(*m);
                } else if (is_sort(e)) {
                    return some_expr(update_sort(e, convert(sort_level(e))));
                } else if (is_constant(e)) {
                    return some_expr(update_constant(e, convert(const_levels(e))));
                } else {
                    return none_expr();
                }
            });
    }

    void mk_expr_mvars(list<expr> const & es) {
        unsigned i = 0;
        for (expr const & e : es) {
            expr e_type = convert(m_ctx.infer(e));
            m_expr2meta.insert(e, mk_idx_metavar(i, e_type));
            i++;
        }
    }

    void check_levels(list<level> const & ls) {
        unsigned i = 1;
        for (level const & l : ls) {
            if (!m_found_levels.contains(l))
                throw exception(sstream() << "invalid mk_pattern, #" << i << " level parameter does not occur in the target or expr parameter types");
            i++;
        }
    }

    void check_exprs(list<expr> const & es) {
        unsigned i = 1;
        for (expr const & e : es) {
            if (!m_found_exprs.contains(e))
                throw exception(sstream() << "invalid mk_pattern, #" << i << " expr parameter does not occur in the target or (other) expr parameter types");
            i++;
        }
    }

    vm_obj mk(list<level> const & ls, list<expr> const & es, expr const & t, list<expr> const & os) {
        mk_level_uvars(ls);
        mk_expr_mvars(es);
        expr target = convert(t);
        check_levels(ls);
        check_exprs(es);
        list<expr> output = map(os, [&](expr const & e) { return convert(e); });
        return mk_pattern(target, output, length(ls), length(es));
    }
};

#define TRY   LEAN_TACTIC_TRY
#define CATCH LEAN_TACTIC_CATCH(to_tactic_state(s))

/*
meta_constant mk_pattern : list level → list expr → expr → list expr → tactic pattern
*/
vm_obj tactic_mk_pattern(vm_obj const & ls, vm_obj const & es, vm_obj const & t, vm_obj const & os, vm_obj const & s) {
    TRY;
    vm_obj pattern = mk_pattern_fn(to_tactic_state(s)).mk(to_list_level(ls), to_list_expr(es), to_expr(t), to_list_expr(os));
    return mk_tactic_success(pattern, to_tactic_state(s));
    CATCH;
}

/*
meta_constant match_pattern_core : transparency → pattern → expr → tactic (list expr)
*/
vm_obj tactic_match_pattern_core(vm_obj const & m, vm_obj const & p, vm_obj const & e, vm_obj const & s) {
    TRY;
    expr t; list<expr> os; unsigned nuvars, nmvars;
    get_pattern_fields(p, t, os, nuvars, nmvars);
    type_context ctx = mk_type_context_for(s, m);
    type_context::tmp_mode_scope scope(ctx, nuvars, nmvars);
    if (ctx.is_def_eq(t, to_expr(e))) {
        buffer<expr> inst_os;
        for (expr const & o : os) {
            inst_os.push_back(ctx.instantiate_mvars(o));
        }
        return mk_tactic_success(to_obj(to_list(inst_os)), to_tactic_state(s));
    } else {
        return mk_tactic_exception("match_pattern failed", to_tactic_state(s));
    }
    CATCH;
}

void initialize_match_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "mk_pattern"}),         tactic_mk_pattern);
    DECLARE_VM_BUILTIN(name({"tactic", "match_pattern_core"}), tactic_match_pattern_core);
}

void finalize_match_tactic() {
}
}