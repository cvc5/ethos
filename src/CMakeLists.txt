file(GLOB alfc_SRC CONFIGURE_DEPENDS "*.h" "*.cpp")

add_executable(alfc ${alfc_SRC})

target_link_libraries(alfc ${LIBRARIES})
