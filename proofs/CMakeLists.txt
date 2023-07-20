set(atc_test_file_list
  theories/ArithBridge.smt2
  theories/BitVectors.smt2
  theories/Core.smt2
  theories/Ints.smt2
  theories/Reals.smt2
)

macro(atc_test file)
  add_test(
    NAME ${file}
    COMMAND $<TARGET_FILE:atc> ${CMAKE_CURRENT_LIST_DIR}/${file}
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
  )
  set_tests_properties(${file} PROPERTIES TIMEOUT 40)
endmacro()

foreach(file ${atc_test_file_list})
  atc_test(${file})
endforeach()