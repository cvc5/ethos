# Build an Ethos executable with a plugin selected by its header and class.
# The generic factory in src/plugin.cpp performs the construction, so plugin
# projects only need to provide their implementation sources.

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
