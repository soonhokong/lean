#include <iostream>
#include <fstream>
#include <signal.h>
#include "version.h"
#include "printer.h"
#include "interruptable_ptr.h"
#include "smt_parser.h"
using namespace lean;

static interruptable_ptr<smt::shell> g_smt_shell;

static void on_ctrl_c(int) {
    g_smt_shell.set_interrupt(true);
}

bool smt_shell() {
    std::cout << "Lean (version " << LEAN_VERSION_MAJOR << "." << LEAN_VERSION_MINOR << ")\n";
    std::cout << "Type Ctrl-D to exit or 'Help.' for help."<< std::endl;
    smt::frontend f;
    smt::shell sh(f);
    scoped_set_interruptable_ptr<smt::shell> set(g_smt_shell, &sh);
    signal(SIGINT, on_ctrl_c);
    return sh();
}

int main(int argc, char ** argv) {
    if (argc == 1) {
        return smt_shell() ? 0 : 1;
    } else {
        bool ok = true;
        smt::frontend f;
        for (int i = 1; i < argc; i++) {
            std::ifstream in(argv[i]);
            smt::parser p(f, in);
            if (!p())
                ok = false;
        }
        return ok ? 0 : 1;
    }
}
