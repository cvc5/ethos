cmake_minimum_required(VERSION 3.12)

project(ethos_cpp_compiler LANGUAGES CXX)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

get_filename_component(ETHOS_SOURCE_DIR "${CMAKE_CURRENT_LIST_DIR}/../.."
                       ABSOLUTE)
set(CMAKE_MODULE_PATH "${ETHOS_SOURCE_DIR}/cmake")

find_package(GMP REQUIRED)
include(EthosPlugin)

ethos_set_default_build_type()

set(ETHOS_CPP_COMPILER_MODE "" CACHE STRING
    "C++ auto-parser mode: compiler, executor, or test")
set_property(CACHE ETHOS_CPP_COMPILER_MODE PROPERTY STRINGS
             compiler executor test)
set(ETHOS_CPP_COMPILER_GENERATED_SOURCE "" CACHE FILEPATH
    "Generated compiled.out.cpp used in executor mode")

ethos_add_core_library(ethos-cpp-core)

if(ETHOS_CPP_COMPILER_MODE STREQUAL "compiler")
  add_ethos_plugin_executable(
    ethos
    PLUGIN_HEADER compiler.h
    PLUGIN_CLASS ethos::Compiler
    SOURCES compiler.cpp)
elseif(ETHOS_CPP_COMPILER_MODE STREQUAL "executor")
  if(NOT ETHOS_CPP_COMPILER_GENERATED_SOURCE)
    message(FATAL_ERROR
      "Executor mode requires ETHOS_CPP_COMPILER_GENERATED_SOURCE")
  endif()
  if(NOT EXISTS "${ETHOS_CPP_COMPILER_GENERATED_SOURCE}")
    message(FATAL_ERROR
      "Generated source does not exist: ${ETHOS_CPP_COMPILER_GENERATED_SOURCE}")
  endif()
  add_ethos_plugin_executable(
    ethos
    PLUGIN_HEADER executor.h
    PLUGIN_CLASS ethos::Executor
    SOURCES executor.cpp "${ETHOS_CPP_COMPILER_GENERATED_SOURCE}")
elseif(NOT ETHOS_CPP_COMPILER_MODE STREQUAL "test")
  message(FATAL_ERROR
    "ETHOS_CPP_COMPILER_MODE must be compiler, executor, or test")
endif()

if(TARGET ethos)
  ethos_configure_target(ethos)
  set_target_properties(ethos PROPERTIES
                        RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/bin")
  target_link_libraries(ethos PRIVATE ethos-cpp-core)
endif()

# Exercise the compiler end to end: parse a signature, compile the generated
# source, reconstruct the parser state, and inspect the reconstructed values.
set(cpp_compiler_test_dir "${CMAKE_BINARY_DIR}/roundtrip")
set(cpp_compiler_test_signature
    "${CMAKE_CURRENT_LIST_DIR}/test/signature.eo")
set(cpp_compiler_test_reference
    "${CMAKE_CURRENT_LIST_DIR}/test/reference.smt2")
set(cpp_compiler_unrelated_signature
    "${CMAKE_CURRENT_LIST_DIR}/test/unrelated/signature.eo")
set(cpp_compiler_relocated_signature
    "${cpp_compiler_test_dir}/relocated/signature.eo")
file(MAKE_DIRECTORY "${cpp_compiler_test_dir}")

add_executable(cpp-compiler-generate EXCLUDE_FROM_ALL
               test/generate.cpp
               compiler.cpp)
ethos_configure_target(cpp-compiler-generate)
target_link_libraries(cpp-compiler-generate PRIVATE ethos-cpp-core)

set(cpp_compiler_generated_source
    "${cpp_compiler_test_dir}/compiled.out.cpp")
add_custom_command(
  OUTPUT "${cpp_compiler_generated_source}"
         "${cpp_compiler_relocated_signature}"
  COMMAND ${CMAKE_COMMAND} -E make_directory
          "${cpp_compiler_test_dir}/relocated"
  COMMAND ${CMAKE_COMMAND} -E copy_if_different
          "${cpp_compiler_test_signature}"
          "${cpp_compiler_relocated_signature}"
  COMMAND $<TARGET_FILE:cpp-compiler-generate>
          "${cpp_compiler_test_signature}"
          "${cpp_compiler_test_reference}"
  DEPENDS cpp-compiler-generate
          "${cpp_compiler_test_signature}"
          "${cpp_compiler_test_reference}"
  WORKING_DIRECTORY "${cpp_compiler_test_dir}"
  COMMENT "Generating C++ auto-parser test source"
  VERBATIM)
set_source_files_properties("${cpp_compiler_generated_source}"
                            PROPERTIES GENERATED TRUE)

add_executable(cpp-compiler-replay EXCLUDE_FROM_ALL
               test/replay.cpp
               executor.cpp
               "${cpp_compiler_generated_source}")
ethos_configure_target(cpp-compiler-replay)
target_compile_definitions(
  cpp-compiler-replay PRIVATE
  ETHOS_CPP_COMPILER_TEST_SIGNATURE="${cpp_compiler_relocated_signature}"
  ETHOS_CPP_COMPILER_TEST_OTHER_SIGNATURE="${cpp_compiler_unrelated_signature}")
target_link_libraries(cpp-compiler-replay PRIVATE ethos-cpp-core)

add_custom_target(cpp-compiler-roundtrip
  COMMAND $<TARGET_FILE:cpp-compiler-replay>
  DEPENDS cpp-compiler-replay "${cpp_compiler_unrelated_signature}"
  COMMENT "Testing generated C++ auto-parser")

enable_testing()
add_test(NAME cpp-compiler-roundtrip COMMAND cpp-compiler-replay)
