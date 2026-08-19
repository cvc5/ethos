# Standalone build for ethos-eoc: the ethos core plus the Eunoia compiler
# plugins in this directory. This is deliberately a separate project so that
# the core ethos build is unaffected by the plugins. From the repository
# root, configure and build with:
#
#   cmake -S plugins -B build-eoc
#   cmake --build build-eoc --target ethos-eoc -j4
#
# The tools/eoc/driver.py script configures and builds this project
# automatically.
cmake_minimum_required (VERSION 3.12)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

macro(add_cxx_flag flag)
  message(STATUS "Configure with flag '${flag}'")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flag}")
endmacro()

project (ethos_eoc)

# the root of the ethos source tree
get_filename_component(ETHOS_ROOT "${PROJECT_SOURCE_DIR}/.." ABSOLUTE)

set (CMAKE_MODULE_PATH ${ETHOS_ROOT}/cmake)

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

# the ethos core, minus its main
file(GLOB_RECURSE ethos_core_SRC CONFIGURE_DEPENDS
  "${ETHOS_ROOT}/src/*.h" "${ETHOS_ROOT}/src/*.cpp")
list(REMOVE_ITEM ethos_core_SRC "${ETHOS_ROOT}/src/main.cpp")

include_directories(${ETHOS_ROOT}/src)

add_executable(ethos-eoc
  ${ethos_core_SRC}
  main_eoc.cpp
  utils.cpp
  std_plugin.cpp
  meta_reduce_plugin.cpp
  desugar/desugar.cpp
  desugar/desugar_checker.cpp
  lean_meta/lean_meta_reduce.cpp
  linear_patterns/linear_patterns.cpp
  model_smt/model_smt.cpp
  smt_meta/smt_meta_reduce.cpp
  smt_meta/smt_meta_sygus.cpp
  smt_meta/utils.cpp
  trim_defs/trim_defs.cpp)

target_link_libraries(ethos-eoc ${LIBRARIES})
target_compile_definitions(
  ethos-eoc PRIVATE ETHOS_PLUGIN_SOURCE_DIR="${ETHOS_ROOT}")
target_compile_definitions(
  ethos-eoc PRIVATE ETHOS_PLUGIN_OUTPUT_DIR="${PROJECT_BINARY_DIR}/out")
