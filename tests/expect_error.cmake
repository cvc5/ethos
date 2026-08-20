set(test_command "${TEST_BINARY}")
if(TEST_MODE STREQUAL "STDIN")
  set(test_input_args INPUT_FILE "${TEST_FILE}")
else()
  if(TEST_MODE)
    list(APPEND test_command "${TEST_MODE}")
  endif()
  list(APPEND test_command "${TEST_FILE}")
endif()

execute_process(
  COMMAND ${test_command}
  ${test_input_args}
  WORKING_DIRECTORY "${TEST_WORKDIR}"
  RESULT_VARIABLE test_result
  OUTPUT_VARIABLE test_stdout
  ERROR_VARIABLE test_stderr
)

set(test_output "${test_stdout}${test_stderr}")

if("${test_result}" STREQUAL "0")
  message(FATAL_ERROR "Expected ${TEST_FILE} to fail, but it succeeded.")
endif()

if(NOT test_output MATCHES "${EXPECT_REGEX}")
  message(FATAL_ERROR
    "Expected output matching `${EXPECT_REGEX}` for ${TEST_FILE}, got:\n${test_output}")
endif()
