#include <fstream>
#include <iostream>

#include "base/output.h"
#include "state.h"

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
      else if (arg=="--no-print-let")
      {
        opts.d_printLet = false;
        readOpt = true;
      }
      else if (arg=="-t")
      {
        i++;
        std::string targ(argv[i]);
#ifdef ALFC_TRACING
        TraceChannel.on(targ);
#else
        std::cerr << "Tracing not enabled in this build" << std::endl;
        exit(1);
#endif
        readOpt = true;
      }
      else if (arg=="-v")
      {
// enable all traces
#ifdef ALFC_TRACING
        TraceChannel.on("compiler");
        TraceChannel.on("expr_parser");
        TraceChannel.on("state");
        TraceChannel.on("type_checker");
#else
        std::cerr << "Tracing not enabled in this build" << std::endl;
        exit(1);
#endif
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
