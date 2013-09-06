add_library(smt_frontend smt_frontend.cpp smt_operator_info.cpp smt_scanner.cpp smt_parser.cpp smt_pp.cpp
  smt_notation.cpp smt_elaborator.cpp smt_elaborator_exception.cpp)
target_link_libraries(smt_frontend ${LEAN_LIBS})
