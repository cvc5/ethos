file(GLOB atc_SRC CONFIGURE_DEPENDS "*.h" "*.cpp")

add_executable(atc ${atc_SRC})
