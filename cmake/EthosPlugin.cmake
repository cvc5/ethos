# Shared CMake infrastructure for the plugin projects under plugins/. These
# are standalone projects that build against the ethos core in src/, so this
# module holds the settings they would otherwise each duplicate: the build
# flags (ethos_configure_target), the build type (ethos_set_default_build_type),
# the ethos core library (ethos_add_core_library), and the single-plugin
# executable driven by the generic factory in src/plugin.cpp
# (add_ethos_plugin_executable).
#
# Callers must find_package(GMP REQUIRED) before including this module.

get_filename_component(ETHOS_PLUGIN_INFRA_SOURCE_DIR
                       "${CMAKE_CURRENT_LIST_DIR}/.." ABSOLUTE)

function(add_ethos_plugin_executable target)
  set(one_value_args PLUGIN_HEADER PLUGIN_CLASS)
  set(multi_value_args SOURCES)
  cmake_parse_arguments(
    ETHOS_PLUGIN "" "${one_value_args}" "${multi_value_args}" ${ARGN})

  if(ETHOS_PLUGIN_UNPARSED_ARGUMENTS)
    message(FATAL_ERROR
      "Unknown arguments for ${target}: ${ETHOS_PLUGIN_UNPARSED_ARGUMENTS}")
  endif()
  if(NOT ETHOS_PLUGIN_PLUGIN_HEADER)
    message(FATAL_ERROR "${target} requires PLUGIN_HEADER")
  endif()
  if(NOT ETHOS_PLUGIN_PLUGIN_CLASS)
    message(FATAL_ERROR "${target} requires PLUGIN_CLASS")
  endif()

  add_executable(
    ${target}
    "${ETHOS_PLUGIN_INFRA_SOURCE_DIR}/src/main.cpp"
    "${ETHOS_PLUGIN_INFRA_SOURCE_DIR}/src/plugin.cpp"
    ${ETHOS_PLUGIN_SOURCES})
  target_compile_definitions(
    ${target} PRIVATE
    ETHOS_PLUGIN_HEADER="${ETHOS_PLUGIN_PLUGIN_HEADER}"
    ETHOS_PLUGIN_CLASS=${ETHOS_PLUGIN_PLUGIN_CLASS})
endfunction()

# Apply the ethos build settings (language standard, include paths, warnings,
# and build-type definitions) to a target of a plugin project. Include paths
# cover the ethos core and the calling project's own source directory.
function(ethos_configure_target target)
  set_target_properties(${target} PROPERTIES
                        CXX_STANDARD 17
                        CXX_STANDARD_REQUIRED YES
                        CXX_EXTENSIONS YES)
  target_include_directories(${target} PRIVATE
                             "${ETHOS_PLUGIN_INFRA_SOURCE_DIR}/src"
                             "${CMAKE_CURRENT_SOURCE_DIR}"
                             "${GMP_INCLUDE_DIR}")
  if(MSVC)
    target_compile_options(${target} PRIVATE /W4)
  else()
    target_compile_options(${target} PRIVATE -Wall -Wno-deprecated)
  endif()
  if(WIN32)
    target_compile_definitions(${target} PRIVATE USE_CPP_FILESYSTEM)
  endif()
  if(CMAKE_BUILD_TYPE STREQUAL "Debug")
    target_compile_definitions(${target} PRIVATE EO_ASSERTIONS EO_TRACING)
  endif()
endfunction()

# Validate CMAKE_BUILD_TYPE for a plugin project, defaulting to Release.
macro(ethos_set_default_build_type)
  if(NOT CMAKE_BUILD_TYPE)
    message(STATUS "Defaulting to release build.")
    set(CMAKE_BUILD_TYPE Release CACHE STRING "" FORCE)
  endif()
  if(NOT CMAKE_BUILD_TYPE STREQUAL "Debug"
     AND NOT CMAKE_BUILD_TYPE STREQUAL "Release")
    message(FATAL_ERROR "Invalid build type '${CMAKE_BUILD_TYPE}'")
  endif()
endmacro()

# Add a static library holding the ethos core: everything under src/ except
# main.cpp and plugin.cpp. Executables bring their own entry point, and
# add_ethos_plugin_executable compiles src/plugin.cpp into the executable
# itself, where the plugin selection macros are defined.
function(ethos_add_core_library target)
  file(GLOB_RECURSE ethos_core_SRC CONFIGURE_DEPENDS
       "${ETHOS_PLUGIN_INFRA_SOURCE_DIR}/src/*.cpp")
  list(FILTER ethos_core_SRC EXCLUDE REGEX "/src/main\\.cpp$")
  list(FILTER ethos_core_SRC EXCLUDE REGEX "/src/plugin\\.cpp$")
  add_library(${target} STATIC ${ethos_core_SRC})
  ethos_configure_target(${target})
  target_link_libraries(${target} PUBLIC ${GMP_LIBRARIES})
endfunction()
