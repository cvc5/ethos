#include <fstream>
#include <iostream>

#include "base/output.h"
#include "base/check.h"
#include "state.h"

using namespace alfc;

int main( int argc, char* argv[] )
{
  Options opts;
  Stats stats;
  // read the options
  size_t i = 1;
  std::string file;
  bool readFile = false;
  size_t nargs = static_cast<size_t>(argc);
  while (i<nargs)
  {
    std::string arg(argv[i]);
    i++;
    if (arg=="--gen-compile")
    {
      opts.d_compile = true;
    }
    else if (arg=="--run-compile")
    {
      opts.d_runCompile = true;
    }
    else if (arg=="--no-print-let")
    {
      opts.d_printLet = false;
    }
    else if (arg=="--stats")
    {
      opts.d_stats = true;
    }
    else if (arg=="-t")
    {
      std::string targ(argv[i]);
      i++;
#ifdef ALFC_TRACING
      TraceChannel.on(targ);
#else
      Unhandled() << "Tracing not enabled in this build" << std::endl;
#endif
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
      Unhandled() << "Tracing not enabled in this build" << std::endl;
#endif
    }
    else if (!readFile)
    {
      file = arg;
      readFile = true;
    }
    else
    {
      Unhandled() << "Mulitple files specified, \"" << file << "\" and \"" << arg << "\"" << std::endl;
    }
  }

  if (!readFile)
  {
    Unhandled() << "No file specified" << std::endl;
  }
  State s(opts, stats);
  // include the file
  s.includeFile(file);
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
  std::cout << stats.toString();
  return 0;
}
