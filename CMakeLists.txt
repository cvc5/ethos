cmake_minimum_required (VERSION 3.12)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

macro(add_cxx_flag flag)
  message(STATUS "Configure with flag '${flag}'")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flag}")
endmacro()

project (ethos_checker)

# >> 2-valued: ON OFF
#    > for options where we don't need to detect if set by user (default: OFF)
option(BUILD_STATIC          "Build static binary" OFF)

# The default binary has no plugin. These cache settings support the
# cpp_compiler's two-stage generator/executor build without changing normal
# Ethos builds.
set(ETHOS_CPP_COMPILER_MODE "none" CACHE STRING
    "C++ auto-parser mode for the ethos binary: none, compiler, or executor")
set_property(CACHE ETHOS_CPP_COMPILER_MODE PROPERTY STRINGS
             none compiler executor)
set(ETHOS_CPP_COMPILER_GENERATED_SOURCE "" CACHE FILEPATH
    "Generated compiled.out.cpp used in cpp_compiler executor mode")

if(BUILD_STATIC)
  set(BUILD_SHARED_LIBS OFF)
  set(CMAKE_FIND_LIBRARY_SUFFIXES .a)
  # Linking system libraries statically is strongly discouraged on macOS.
  # See https://developer.apple.com/library/archive/qa/qa1118/_index.html
  if(NOT APPLE)
    set(CMAKE_EXE_LINKER_FLAGS "-static")
  endif()
endif()

set (CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)

find_package(GMP REQUIRED)
set(LIBRARIES ${LIBRARIES} ${GMP_LIBRARIES})
include_directories(${GMP_INCLUDE_DIR})

if(NOT CMAKE_BUILD_TYPE)
  message(STATUS "Defaulting to release build.")
  set(CMAKE_BUILD_TYPE Release CACHE STRING "" FORCE)
endif()

add_cxx_flag("-Wall")
add_cxx_flag("-Wno-deprecated")
add_cxx_flag("-std=gnu++17")

if(WIN32)
  add_definitions(-DUSE_CPP_FILESYSTEM)
endif()

if(CMAKE_BUILD_TYPE STREQUAL "Debug")
  add_cxx_flag("-g")
  add_definitions(-DEO_ASSERTIONS)
  add_definitions(-DEO_TRACING)
  message(STATUS "Configured debug build.")
elseif(CMAKE_BUILD_TYPE STREQUAL "Release")
  message(STATUS "Configured release build.")
else()
  message(FATAL_ERROR "Invalid build type '${CMAKE_BUILD_TYPE}'")
endif()

enable_testing()

include_directories(src)
add_subdirectory(src)
add_subdirectory(tests)

# Build and test the experimental extensions in plugins/. Those are not part
# of ethos, so this target lets CI catch them bitrotting against src/. It is
# EXCLUDE_FROM_ALL, so an ordinary build never sees it. Build it explicitly
# with:
#
#   make plugins-compile-check
#
file(GLOB_RECURSE plugins_SRC CONFIGURE_DEPENDS "plugins/*.cpp")
list(FILTER plugins_SRC EXCLUDE REGEX "/plugins/cpp_compiler/test/")
if(plugins_SRC)
  add_library(plugins-compile-check OBJECT EXCLUDE_FROM_ALL ${plugins_SRC})
else()
  add_custom_target(plugins-compile-check
    COMMAND ${CMAKE_COMMAND} -E echo "No plugin sources to check.")
endif()

# Exercise the C++ compiler end to end: parse a signature with Compiler,
# compile the emitted source, then load it with Executor and check that parser
# state was reconstructed while program evaluation still uses the interpreter.
set(cpp_compiler_test_dir "${CMAKE_CURRENT_BINARY_DIR}/cpp_compiler_test")
set(cpp_compiler_test_signature
    "${CMAKE_CURRENT_SOURCE_DIR}/plugins/cpp_compiler/test/signature.eo")
file(MAKE_DIRECTORY "${cpp_compiler_test_dir}")

file(GLOB_RECURSE cpp_compiler_core_SRC CONFIGURE_DEPENDS "src/*.cpp")
list(FILTER cpp_compiler_core_SRC EXCLUDE REGEX "/src/main\\.cpp$")
add_library(cpp-compiler-test-core STATIC EXCLUDE_FROM_ALL
            ${cpp_compiler_core_SRC})
target_link_libraries(cpp-compiler-test-core PUBLIC ${LIBRARIES})

add_executable(cpp-compiler-generate EXCLUDE_FROM_ALL
  plugins/cpp_compiler/test/generate.cpp
  plugins/cpp_compiler/compiler.cpp)
target_include_directories(cpp-compiler-generate PRIVATE
                           plugins/cpp_compiler)
target_link_libraries(cpp-compiler-generate PRIVATE cpp-compiler-test-core)

set(cpp_compiler_generated_source
    "${cpp_compiler_test_dir}/compiled.out.cpp")
add_custom_command(
  OUTPUT "${cpp_compiler_generated_source}"
  COMMAND $<TARGET_FILE:cpp-compiler-generate>
          "${cpp_compiler_test_signature}"
  DEPENDS cpp-compiler-generate "${cpp_compiler_test_signature}"
  WORKING_DIRECTORY "${cpp_compiler_test_dir}"
  COMMENT "Generating C++ auto-parser test source"
  VERBATIM)
set_source_files_properties("${cpp_compiler_generated_source}"
                            PROPERTIES GENERATED TRUE)

add_executable(cpp-compiler-replay EXCLUDE_FROM_ALL
  plugins/cpp_compiler/test/replay.cpp
  plugins/cpp_compiler/executor.cpp
  "${cpp_compiler_generated_source}")
target_include_directories(cpp-compiler-replay PRIVATE plugins/cpp_compiler)
target_compile_definitions(
  cpp-compiler-replay PRIVATE
  ETHOS_CPP_COMPILER_TEST_SIGNATURE="${cpp_compiler_test_signature}")
target_link_libraries(cpp-compiler-replay PRIVATE cpp-compiler-test-core)

add_custom_target(cpp-compiler-roundtrip
  COMMAND $<TARGET_FILE:cpp-compiler-replay>
  DEPENDS cpp-compiler-replay
  COMMENT "Testing generated C++ auto-parser")
add_dependencies(plugins-compile-check cpp-compiler-roundtrip)
