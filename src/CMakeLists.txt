file(GLOB_RECURSE ethos_SRC CONFIGURE_DEPENDS "*.h" "*.cpp")

add_executable(ethos ${ethos_SRC}
../plugins/smt_meta/smt_meta_reduce.cpp
../plugins/desugar/desugar.cpp
../plugins/trim_defs/trim_defs.cpp)

target_link_libraries(ethos ${LIBRARIES})
