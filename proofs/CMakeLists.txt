set(alfc_test_file_list
  theories/Arith.smt2
  theories/BitVectors.smt2
  theories/Builtin.smt2
  theories/Ints.smt2
  theories/Reals.smt2
  theories/Strings.smt2
  rules/Arith.smt2
  rules/Uf.smt2
  rules/Booleans.smt2
  rules/Strings.smt2
  examples/simple_uf.smt2
  examples/booleans.smt2
  examples/nary.smt2
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
