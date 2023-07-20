#include "state.h"

#include <iostream>

using namespace atc;

int main( int argc, char* argv[] )
{
  if (argc!=2)
  {
    std::cerr << "Usage" << std::endl;
    exit(1);
  }
  // include the file
  State s;
  s.includeFile(argv[1]);
  std::cout << "success" << std::endl;
  return 0;
}
