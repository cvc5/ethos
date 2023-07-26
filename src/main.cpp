#include "state.h"

#include <iostream>

using namespace alfc;

int main( int argc, char* argv[] )
{
  Options opts;
  // read the options
  bool readOpt = false;
  size_t i = 0;
  size_t nargs = static_cast<size_t>(argc);
  do
  {
    i++;
    readOpt = false;
    if (i<nargs)
    {
      std::string arg(argv[i]);
      if (arg=="--compile")
      {
        opts.d_compile = true;
        readOpt = true;
      }
      else if (arg=="--run-compile")
      {
        opts.d_runCompile = true;
        readOpt = true;
      }
    }
  }while(readOpt);

  if (nargs!=i+1)
  {
    std::cerr << "Usage: " << argv[0] << " <options>* <file>" << std::endl;
    exit(1);
  }
  // include the file
  State s(opts);
  s.includeFile(argv[1]);
  std::cout << "success" << std::endl;
  return 0;
}
