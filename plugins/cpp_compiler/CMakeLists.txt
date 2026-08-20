cmake_minimum_required(VERSION 3.12)

project(ethos_cpp_compiler LANGUAGES CXX)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

get_filename_component(ETHOS_SOURCE_DIR "${CMAKE_CURRENT_LIST_DIR}/../.."
                       ABSOLUTE)
set(CMAKE_MODULE_PATH "${ETHOS_SOURCE_DIR}/cmake")

find_package(GMP REQUIRED)

if(NOT CMAKE_BUILD_TYPE)
  message(STATUS "Defaulting to release build.")
  set(CMAKE_BUILD_TYPE Release CACHE STRING "" FORCE)
endif()

set(ETHOS_CPP_COMPILER_MODE "" CACHE STRING
    "C++ auto-parser mode: compiler or executor")
set_property(CACHE ETHOS_CPP_COMPILER_MODE PROPERTY STRINGS compiler executor)
set(ETHOS_CPP_COMPILER_GENERATED_SOURCE "" CACHE FILEPATH
    "Generated compiled.out.cpp used in executor mode")

file(GLOB_RECURSE ethos_SRC CONFIGURE_DEPENDS
     "${ETHOS_SOURCE_DIR}/src/*.h"
     "${ETHOS_SOURCE_DIR}/src/*.cpp")
add_executable(ethos ${ethos_SRC})
set_target_properties(ethos PROPERTIES
                      CXX_STANDARD 17
                      CXX_STANDARD_REQUIRED YES
                      CXX_EXTENSIONS YES
                      RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/bin")
target_include_directories(ethos PRIVATE
                           "${ETHOS_SOURCE_DIR}/src"
                           "${CMAKE_CURRENT_LIST_DIR}"
                           "${GMP_INCLUDE_DIR}")
target_link_libraries(ethos PRIVATE ${GMP_LIBRARIES})

if(MSVC)
  target_compile_options(ethos PRIVATE /W4)
else()
  target_compile_options(ethos PRIVATE -Wall -Wno-deprecated)
endif()

if(WIN32)
  target_compile_definitions(ethos PRIVATE USE_CPP_FILESYSTEM)
endif()

if(CMAKE_BUILD_TYPE STREQUAL "Debug")
  target_compile_definitions(ethos PRIVATE EO_ASSERTIONS EO_TRACING)
elseif(NOT CMAKE_BUILD_TYPE STREQUAL "Release")
  message(FATAL_ERROR "Invalid build type '${CMAKE_BUILD_TYPE}'")
endif()

if(ETHOS_CPP_COMPILER_MODE STREQUAL "compiler")
  target_sources(ethos PRIVATE compiler.cpp)
  target_compile_definitions(ethos PRIVATE ETHOS_CPP_COMPILER_GENERATOR)
elseif(ETHOS_CPP_COMPILER_MODE STREQUAL "executor")
  if(NOT ETHOS_CPP_COMPILER_GENERATED_SOURCE)
    message(FATAL_ERROR
      "Executor mode requires ETHOS_CPP_COMPILER_GENERATED_SOURCE")
  endif()
  if(NOT EXISTS "${ETHOS_CPP_COMPILER_GENERATED_SOURCE}")
    message(FATAL_ERROR
      "Generated source does not exist: ${ETHOS_CPP_COMPILER_GENERATED_SOURCE}")
  endif()
  target_sources(ethos PRIVATE
                 executor.cpp
                 "${ETHOS_CPP_COMPILER_GENERATED_SOURCE}")
  target_compile_definitions(ethos PRIVATE ETHOS_CPP_COMPILER_EXECUTOR)
else()
  message(FATAL_ERROR
    "ETHOS_CPP_COMPILER_MODE must be compiler or executor")
endif()
