#include "state.h"

#include <iostream>
#include <fstream>

using namespace alfc;

int main( int argc, char* argv[] )
{
  Options opts;
  Stats stats;
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
      if (arg=="--gen-compile")
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
  State s(opts, stats);
  // include the file
  s.includeFile(argv[i]);
  std::cout << "success" << std::endl;
  if (opts.d_compile)
  {
    Compiler * c = s.getCompiler();
    std::fstream fs("compiled.out.cpp", std::ios::out);
    fs << "/** ================ AUTO GENERATED ============ */" << std::endl;
    fs << c->toString() << std::endl;
    fs.close();
    std::cout << "GEN-COMPILE" << std::endl;
    std::cout << c->toString() << std::endl;
  }
  std::cout << "----" << std::endl;
  std::cout << stats.toString();
  std::cout << "----" << std::endl;
  return 0;
}
