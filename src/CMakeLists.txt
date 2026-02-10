file(GLOB_RECURSE ethos_SRC CONFIGURE_DEPENDS "*.h" "*.cpp")

add_executable(ethos ${ethos_SRC}
../plugins/lean_meta/lean_meta_reduce.cpp
../plugins/smt_meta/smt_meta_reduce.cpp
../plugins/smt_meta/smt_meta_sygus.cpp
../plugins/smt_meta/utils.cpp
../plugins/desugar/desugar.cpp
../plugins/desugar/desugar_proof.cpp
../plugins/trim_defs/trim_defs.cpp
../plugins/model_smt/model_smt.cpp
../plugins/flatten_eval/flatten_eval.cpp
../plugins/linear_patterns/linear_patterns.cpp
../plugins/std_plugin.cpp)

target_link_libraries(ethos ${LIBRARIES})
