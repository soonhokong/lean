add_library(smt_frontend frontend.cpp operator_info.cpp scanner.cpp parser.cpp pp.cpp
  notation.cpp elaborator.cpp elaborator_exception.cpp)
target_link_libraries(smt_frontend ${LEAN_LIBS})
