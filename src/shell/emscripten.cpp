/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura, Soonho Kong
*/
#include <string>
#include "util/lean_path.h"
#include "library/module.h"
#include "library/hott_kernel.h"
#include "library/standard_kernel.h"
#include "library/type_context.h"
#include "library/error_handling.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/parser.h"
#include "init/init.h"
#include "shell/simple_pos_info_provider.h"

namespace lean {
class emscripten_shell {
private:
    unsigned trust_lvl;
    unsigned num_threads;
    options opts;
    environment env;
    io_state ios;

public:
    emscripten_shell(bool const use_hott) : trust_lvl(LEAN_BELIEVER_TRUST_LEVEL+1), num_threads(1), opts("flycheck", true),
                                            env(use_hott ? mk_hott_environment(trust_lvl) : mk_environment(trust_lvl)),
                                            ios(opts, lean::mk_pretty_formatter_factory()) {
    }

    int import_module(std::string mname) {
        try {
            module_name mod(mname);
            std::string base = ".";
            bool num_threads = 1;
            bool keep_proofs = false;
            env = import_modules(env, base, 1, &mod, num_threads, keep_proofs, ios);
        } catch (lean::exception & ex) {
            simple_pos_info_provider pp("import_module");
            type_context tc(env, ios.get_options());
            auto out = diagnostic(env, ios, tc);
            lean::display_error(out, &pp, ex);
            return 1;
        }
        return 0;
    }

    int process_file(std::string input_filename) {
        bool ok = true;
        try {
            environment temp_env(env);
            io_state    temp_ios(ios);
            if (!parse_commands(temp_env, temp_ios, input_filename.c_str(), optional<std::string>(), false, num_threads)) {
                ok = false;
            }
        } catch (lean::exception & ex) {
            simple_pos_info_provider pp(input_filename.c_str());
            ok = false;
            type_context tc(env, ios.get_options());
            auto out = diagnostic(env, ios, tc);
            lean::display_error(out, &pp, ex);
        }
        return ok ? 0 : 1;
    }
};
}

static lean::initializer * g_init = nullptr;
static lean::emscripten_shell * g_shell = nullptr;

void initialize_emscripten(bool use_hott) {
    g_init  = new lean::initializer();
    if (use_hott) {
        lean::initialize_lean_path(true);
    }
    g_shell = new lean::emscripten_shell(use_hott);
}

void finalize_emscripten() {
    delete g_shell;
    delete g_init;
}

int emscripten_import_module(std::string mname) {
    return g_shell->import_module(mname);
}

int emscripten_process_file(std::string input_filename) {
    return g_shell->process_file(input_filename);
}
