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

project (ethos_eoc LANGUAGES CXX)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

get_filename_component(ETHOS_SOURCE_DIR "${CMAKE_CURRENT_LIST_DIR}/.." ABSOLUTE)
set(CMAKE_MODULE_PATH "${ETHOS_SOURCE_DIR}/cmake")

find_package(GMP REQUIRED)
include(EthosPlugin)

ethos_set_default_build_type()

ethos_add_core_library(ethos-eoc-core)

# Every plugin source in this directory, matching the plugins-compile-check
# target in the top-level CMakeLists.txt so that the two cannot drift: a new
# plugin source is picked up by both. cpp_compiler is its own project, see
# cpp_compiler/CMakeLists.txt.
file(GLOB_RECURSE ethos_eoc_SRC CONFIGURE_DEPENDS
     "${CMAKE_CURRENT_LIST_DIR}/*.cpp")
list(FILTER ethos_eoc_SRC EXCLUDE REGEX "/cpp_compiler/")

add_executable(ethos-eoc ${ethos_eoc_SRC})
ethos_configure_target(ethos-eoc)
target_link_libraries(ethos-eoc PRIVATE ethos-eoc-core)

# Where the plugins read their .eo/.lean inputs from and write their outputs
# to, see StdPlugin::getSourceDirectory and StdPlugin::getOutputDirectory.
target_compile_definitions(
  ethos-eoc PRIVATE
  ETHOS_PLUGIN_SOURCE_DIR="${ETHOS_SOURCE_DIR}"
  ETHOS_PLUGIN_OUTPUT_DIR="${PROJECT_BINARY_DIR}/out")
