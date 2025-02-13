#!/usr/bin/env bash
#--------------------------------------------------------------------------#

set -e -o pipefail

usage () {
cat <<EOF
Usage: $0 [<build type>] [<option> ...]

Build types:
  release
  debug


General options;
  -h, --help               display this help and exit
  --prefix=STR             install directory
  --name=STR               use custom build directory name (optionally: +path)


Features:
The following flags enable optional features (disable with --no-<option name>).
  --static                 build static binary [default=no]


CMake Options (Advanced)
  -DVAR=VALUE              manually add CMake options

EOF
  exit 0
}

#--------------------------------------------------------------------------#

die () {
  echo "*** configure.sh: $*" 1>&2
  exit 1
}

msg () {
  echo "[configure.sh] $*"
}

#--------------------------------------------------------------------------#

[ ! -e src ] && die "$0 not called from ethos base directory"

#--------------------------------------------------------------------------#

build_dir=build
install_prefix=default

#--------------------------------------------------------------------------#

buildtype=default

build_static=default

#--------------------------------------------------------------------------#

cmake_opts=""

while [ $# -gt 0 ]
do
  case $1 in

    -h|--help) usage;;

    --prefix) die "missing argument to $1 (try -h)" ;;
    --prefix=*)
        install_prefix=${1##*=}
        # Check if install_prefix is an absolute path and if not, make it
        # absolute.
        case $install_prefix in
          /*) ;;                                      # absolute path
          *) install_prefix=$(pwd)/$install_prefix ;; # make absolute path
        esac
        ;;

    --name) die "missing argument to $1 (try -h)" ;;
    --name=*) build_dir=${1##*=} ;;

    --static) build_static=ON;;
    --no-static) build_static=OFF;;

    -D*) cmake_opts="${cmake_opts} $1" ;;

    -*) die "invalid option '$1' (try -h)";;

    *) case $1 in
         release)         buildtype=Release;;
         debug)           buildtype=Debug;;
         *)               die "invalid build type (try -h)";;
       esac
       ;;
  esac
  shift
done

#--------------------------------------------------------------------------#

[ $buildtype != default ] \
  && cmake_opts="$cmake_opts -DCMAKE_BUILD_TYPE=$buildtype"
[ "$install_prefix" != default ] \
  && cmake_opts="$cmake_opts -DCMAKE_INSTALL_PREFIX=$install_prefix"
[ $build_static != default ] \
  && cmake_opts="$cmake_opts -DBUILD_STATIC=$build_static"

uname_output=$(uname)
[[ $uname_output =~ ^MSYS || $uname_output =~ ^MINGW ]] \
  && export CMAKE_GENERATOR="MSYS Makefiles"

root_dir=$(pwd)

mkdir -p "$build_dir"

cd "$build_dir"

[ -e CMakeCache.txt ] && rm CMakeCache.txt
build_dir_escaped=$(echo "$build_dir" | sed 's/\//\\\//g')
cmake "$root_dir" $cmake_opts 2>&1 | \
  sed "s/^Now just/Now change to '$build_dir_escaped' and/"
