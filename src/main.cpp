/******************************************************************************
 * This file is part of the alfc project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include <unistd.h>
#include <iomanip>
#include <iostream>

#include "base/check.h"
#include "base/output.h"
#include "parser.h"
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
    if (arg=="--binder-fresh")
    {
      opts.d_binderFresh = true;
    }
    else if (arg=="--no-parse-let")
    {
      opts.d_parseLet = false;
    }
    else if (arg=="--no-print-let")
    {
      opts.d_printLet = false;
    }
    else if (arg=="--stats")
    {
      opts.d_stats = true;
    }
    else if (arg=="--stats-compact")
    {
      opts.d_stats = true;
      opts.d_statsCompact = true;
    }
    else if (arg=="--no-rule-sym-table")
    {
      opts.d_ruleSymTable = false;
    }
    else if (arg=="--no-normalize-dec")
    {
      opts.d_normalizeDecimal = false;
    }
    else if (arg=="--no-normalize-hex")
    {
      opts.d_normalizeHexadecimal = false;
    }
    else if (arg=="--help")
    {
      std::stringstream out;
      out << "     --binder-fresh: binders generate fresh variables when parsed in proof files." << std::endl;
      out << "             --help: displays this message." << std::endl;
      out << " --no-normalize-dec: do not treat decimal literals as syntax sugar for rational literals." << std::endl;
      out << " --no-normalize-hex: do not treat hexadecimal literals as syntax sugar for binary literals." << std::endl;
      out << "     --no-parse-let: do not treat let as a builtin symbol for specifying terms having shared subterms." << std::endl;
      out << "     --no-print-let: do not letify the output of terms in error messages and trace messages." << std::endl;
      out << "--no-rule-sym-table: do not use a separate symbol table for proof rules and declared terms." << std::endl;
      out << "      --show-config: displays the build information for this binary." << std::endl;
      out << "            --stats: enables detailed statistics." << std::endl;
      out << "    --stats-compact: print statistics in a compact format." << std::endl;
      out << "           -t <tag>: enables the given trace tag (requires debug build)." << std::endl;
      out << "                 -v: verbose mode, enable all standard trace messages (requires debug build)." << std::endl;
      std::cout << out.str();
      return 0;
    }
    else if (arg=="--show-config")
    {
      std::stringstream out;
      out << "This is alfc version 0.0." << std::endl;
      out << std::endl;
      size_t w = 15;
      out << std::setw(w) << "tracing : ";
#ifdef ALFC_TRACING
      out << "yes";
#else
      out << "no";
#endif
      out << std::endl;
      std::cout << out.str();
      return 0;
    }
    else if (arg=="-t")
    {
      std::string targ(argv[i]);
      i++;
#ifdef ALFC_TRACING
      TraceChannel.on(targ);
#else
      ALFC_FATAL() << "Error: tracing not enabled in this build" << std::endl;
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
      TraceChannel.on("compile");
      TraceChannel.on("step");
#else
      ALFC_FATAL() << "Error: tracing not enabled in this build";
#endif
    }
    else if (!readFile)
    {
      file = arg;
      readFile = true;
    }
    else
    {
      // maybe one of these is a wrong option
      for (size_t i=0; i<2; i++)
      {
        std::string oarg(i==0 ? file : arg);
        if (oarg.compare(0, 2, "--")==0)
        {
          ALFC_FATAL() << "Error: unrecognized option " << oarg;
        }
      }
      ALFC_FATAL() << "Error: mulitple files specified, \"" << file << "\" and \"" << arg << "\"";
    }
  }
  State s(opts, stats);
  Plugin * plugin = nullptr;
  // NOTE: initialization of plugin goes here
  if (plugin!=nullptr)
  {
    s.setPlugin(plugin);
  }
  if (!readFile)
  {
    // no file, either std::in is piped, or the user forgot to provide an input
    if (isatty(fileno(stdin)))
    {
      ALFC_FATAL() << "Error: no input specified.";
    }
    // parse from std::cin.
    Parser p(s, false);
    p.setStreamInput(std::cin);
    // parse commands until finished
    while (p.parseNextCommand())
    {
    }
  }
  else
  {
    // include the file
    if (!s.includeFile(file))
    {
      ALFC_FATAL() << "Error: cannot include file " << file;
    }
  }
  bool wasIncomplete = false;
  std::map<const ExprValue*, RuleStat>& rs = stats.d_rstats;
  for (const std::pair<const ExprValue* const, RuleStat>& r : rs)
  {
    if (s.isProofRuleSorry(r.first))
    {
      wasIncomplete = true;
      break;
    }
  }
  if (wasIncomplete)
  {
    std::cout << "incomplete" << std::endl;
  }
  else
  {
    // TODO: to be renamed "correct"
    std::cout << "success" << std::endl;
  }
  if (plugin != nullptr)
  {
    plugin->finalize();
  }
  if (opts.d_stats)
  {
    std::cout << stats.toString(s, opts.d_statsCompact);
  }
  // exit immediately, which avoids deleting all expressions which can take time
  exit(0);
  return 0;
}
