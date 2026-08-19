file(GLOB_RECURSE ethos_SRC CONFIGURE_DEPENDS "*.h" "*.cpp")

add_executable(ethos ${ethos_SRC})

if(ETHOS_CPP_COMPILER_MODE STREQUAL "compiler")
  target_sources(ethos PRIVATE
                 "${PROJECT_SOURCE_DIR}/plugins/cpp_compiler/compiler.cpp")
  target_include_directories(ethos PRIVATE
                             "${PROJECT_SOURCE_DIR}/plugins/cpp_compiler")
  target_compile_definitions(ethos PRIVATE
                             ETHOS_CPP_COMPILER_GENERATOR)
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
    "${PROJECT_SOURCE_DIR}/plugins/cpp_compiler/executor.cpp"
    "${ETHOS_CPP_COMPILER_GENERATED_SOURCE}")
  target_include_directories(ethos PRIVATE
                             "${PROJECT_SOURCE_DIR}/plugins/cpp_compiler")
  target_compile_definitions(ethos PRIVATE
                             ETHOS_CPP_COMPILER_EXECUTOR)
elseif(NOT ETHOS_CPP_COMPILER_MODE STREQUAL "none")
  message(FATAL_ERROR
    "Invalid ETHOS_CPP_COMPILER_MODE: ${ETHOS_CPP_COMPILER_MODE}")
endif()

target_link_libraries(ethos ${LIBRARIES})
