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
    pf-substitution.smt2
    substitution-binary-only.smt2
    beta-reduce-define-fun.smt2
    define-const-simple.smt2
    naive-nary.smt2
    sig-replAll.smt2
    pf-sig-replAll.smt2
    simple-sig.smt2
    pf-simple-sig.smt2
    simple-sig-2.smt2
    pf-simple-sig-2.smt2
    not_and.smt2
    scopes.smt2
    substitution-over-or.smt2
    pf-substitution-over-or.smt2
    pf-substitution-large.smt2
    pairwise.smt2
    overloading.smt2
    evaluation.smt2
    bv-concat.smt2
    mixed-arith.smt2
    eval-inc.smt2
    arith-eval.smt2
    pf-arith-eval.smt2
    datatype-simple.smt2
    quant.smt2
    pf-quant.smt2
    bv-type-strict.smt2
    bv-literals.smt2
    bv-eval.smt2
    pf-haniel.smt2
    premise-list-cong.smt2
)

macro(alfc_test file)
  add_test(
    NAME ${file}
    COMMAND $<TARGET_FILE:alfc> --no-print-let ${CMAKE_CURRENT_LIST_DIR}/${file}
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
  )
  set_tests_properties(${file} PROPERTIES TIMEOUT 40)
endmacro()

foreach(file ${alfc_test_file_list})
  alfc_test(${file})
endforeach()

