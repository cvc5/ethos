file(GLOB_RECURSE alfc_SRC CONFIGURE_DEPENDS "*.h" "*.cpp")

add_executable(alfc ${alfc_SRC})
