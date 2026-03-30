file(GLOB_RECURSE ethos_SRC CONFIGURE_DEPENDS "*.h" "*.cpp")

list(REMOVE_ITEM ethos_SRC
  "${CMAKE_CURRENT_SOURCE_DIR}/main.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/main_eoc.cpp")

add_library(ethos_core OBJECT ${ethos_SRC})

add_executable(ethos
  $<TARGET_OBJECTS:ethos_core>
  main.cpp)

add_executable(ethos-eoc EXCLUDE_FROM_ALL
  $<TARGET_OBJECTS:ethos_core>
  main_eoc.cpp
  ../plugins/lean_meta/lean_meta_reduce.cpp
  ../plugins/smt_meta/smt_meta_reduce.cpp
  ../plugins/smt_meta/smt_meta_sygus.cpp
  ../plugins/smt_meta/utils.cpp
  ../plugins/desugar/desugar.cpp
  ../plugins/desugar/desugar_proof.cpp
  ../plugins/desugar/desugar_checker.cpp
  ../plugins/trim_defs/trim_defs.cpp
  ../plugins/model_smt/model_smt.cpp
  ../plugins/flatten_eval/flatten_eval.cpp
  ../plugins/linear_patterns/linear_patterns.cpp
  ../plugins/std_plugin.cpp)

target_link_libraries(ethos ${LIBRARIES})
target_link_libraries(ethos-eoc ${LIBRARIES})
target_compile_definitions(
  ethos-eoc PRIVATE ETHOS_EOC_SOURCE_DIR="${PROJECT_SOURCE_DIR}")
target_compile_definitions(
  ethos-eoc PRIVATE ETHOS_EOC_OUTPUT_DIR="${PROJECT_BINARY_DIR}/out")
