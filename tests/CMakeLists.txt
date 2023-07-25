set(alfc_test_file_list
    Bools.smt2
    literals.smt2
    simple-pf2.smt2
    simple.smt2
    bv-dep-type.smt2
    quoted.smt2
    simple-pf-implicit.smt2
    requires.smt2
    simple-pf.smt2
    evaluate.smt2
    simple-include.smt2
    simple-program.smt2
    generic-swap.smt2
    or-list.smt2
    or-list-null-term.smt2
    or-repl-all.smt2
    or-repl-all-basic.smt2
    constant-eval.smt2
    constant-eval-args.smt2
    chainable.smt2
    substitution.smt2
    substitution-binary-only.smt2
)

macro(alfc_test file)
  add_test(
    NAME ${file}
    COMMAND $<TARGET_FILE:alfc> ${CMAKE_CURRENT_LIST_DIR}/${file}
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
  )
  set_tests_properties(${file} PROPERTIES TIMEOUT 40)
endmacro()

foreach(file ${alfc_test_file_list})
  alfc_test(${file})
endforeach()

