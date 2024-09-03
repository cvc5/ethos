file(GLOB_RECURSE ethos_SRC CONFIGURE_DEPENDS "*.h" "*.cpp")

if(NOT EO_ORACLES)
  # Remove run.h and run.cpp from ethos_SRC
  list(FILTER ethos_SRC EXCLUDE REGEX ".*[/\\]run\\.h$")
  list(FILTER ethos_SRC EXCLUDE REGEX ".*[/\\]run\\.cpp$")
endif()

add_executable(ethos ${ethos_SRC})

target_link_libraries(ethos ${LIBRARIES})
