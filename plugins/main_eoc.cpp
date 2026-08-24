/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

/*
 * Driver for ethos-eoc, the ethos core extended with the Eunoia compiler
 * plugins in this directory. It is built as a standalone project (see
 * plugins/CMakeLists.txt) and is typically invoked via tools/eoc/driver.py,
 * e.g.:
 *
 *   ethos-eoc --plugin.desugar <file>
 *   ethos-eoc --plugin.model-smt --defs=<file> <file>
 *   ethos-eoc --plugin.lean-meta --lean-config=<file> <file>
 *
 * With no --plugin.* argument, it parses the given file like plain ethos.
 * Unlike the plain ethos binary, it requires a file argument (no stdin mode)
 * and does not print a proof checking verdict; a run is successful iff the
 * exit code is 0.
 */

#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "base/check.h"
#include "base/output.h"
#include "state.h"

#include "desugar/desugar.h"
#include "lean_meta/lean_meta_reduce.h"
#include "model_smt/model_smt.h"
#include "smt_meta/smt_meta_reduce.h"
#include "trim_defs/trim_defs.h"

using namespace ethos;

namespace {

std::unique_ptr<Plugin> createPlugin(const std::string& name,
                                     State& s,
                                     bool generateParser,
                                     const std::string& defsFile,
                                     const std::string& leanConfigFile)
{
  if (name == "desugar")
  {
    return std::make_unique<Desugar>(s);
  }
  if (name == "desugar-vc")
  {
    return std::make_unique<Desugar>(s, /*genVcs=*/true);
  }
  if (name == "smt-meta")
  {
    return std::make_unique<SmtMetaReduce>(s);
  }
  if (name == "smt-meta-sygus")
  {
    return std::make_unique<SmtMetaReduce>(s, /*sygus=*/true);
  }
  if (name == "lean-meta")
  {
    return std::make_unique<LeanMetaReduce>(s, generateParser, leanConfigFile);
  }
  if (name == "trim-defs")
  {
    return std::make_unique<TrimDefs>(s);
  }
  if (name == "model-smt")
  {
    return std::make_unique<ModelSmt>(s, defsFile);
  }
  EO_FATAL() << "Error: unknown plugin \"" << name
             << "\" (available: desugar, desugar-vc, smt-meta, "
                "smt-meta-sygus, lean-meta, trim-defs, model-smt)";
  return nullptr;
}

}  // namespace

int main(int argc, char* argv[])
{
  Options opts;
  std::string file;
  bool readFile = false;
  std::string pluginName;
  bool generateParser = true;
  std::string defsFile;
  std::string leanConfigFile;
  // the list of includes and whether they were an include or reference
  std::vector<std::pair<std::string, bool>> includes;
  size_t i = 1;
  size_t nargs = static_cast<size_t>(argc);
  while (i < nargs)
  {
    std::string arg(argv[i]);
    i++;
    if (arg.compare(0, 9, "--plugin.") == 0)
    {
      if (!pluginName.empty())
      {
        EO_FATAL() << "Error: multiple plugins specified, \"" << pluginName
                   << "\" and \"" << arg.substr(9) << "\"";
      }
      pluginName = arg.substr(9);
      continue;
    }
    if (arg == "--no-parser")
    {
      generateParser = false;
      continue;
    }
    if (arg.compare(0, 7, "--defs=") == 0)
    {
      // The signature of the input written in the deep embedding, which says
      // what each of its symbols means to the model. It is read by the
      // model-smt plugin alone; no stage before that one sees it.
      defsFile = arg.substr(7);
      continue;
    }
    if (arg.compare(0, 14, "--lean-config=") == 0)
    {
      // What the input signature needs said about its generated Lean that the
      // compiler cannot derive, namely why each of its recursive programs
      // terminates. It is read by the lean-meta plugin alone.
      leanConfigFile = arg.substr(14);
      continue;
    }
    if (arg.compare(0, 5, "--no-") == 0)
    {
      if (opts.setOption(arg.substr(5), false))
      {
        continue;
      }
    }
    else if (arg.compare(0, 2, "--") == 0)
    {
      if (opts.setOption(arg.substr(2), true))
      {
        continue;
      }
    }
    bool isInclude = (arg.compare(0, 10, "--include=") == 0);
    if (isInclude || arg.compare(0, 12, "--reference=") == 0)
    {
      // defer the inclusion until the options are finalized
      size_t first = arg.find_first_of("=");
      std::string ifile = arg.substr(first + 1);
      includes.emplace_back(ifile, isInclude);
      continue;
    }
    if (arg == "-t")
    {
      if (i >= nargs)
      {
        EO_FATAL() << "Error: Missing trace tag.";
      }
      std::string targ(argv[i]);
      i++;
#ifdef EO_TRACING
      TraceChannel.on(targ);
#else
      EO_FATAL() << "Error: tracing not enabled in this build";
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
      for (size_t j = 0; j < 2; j++)
      {
        std::string oarg(j == 0 ? file : arg);
        if (oarg.compare(0, 2, "--") == 0)
        {
          EO_FATAL() << "Error: unrecognized option " << oarg;
        }
      }
      EO_FATAL() << "Error: multiple files specified, \"" << file << "\" and \""
                 << arg << "\"";
    }
  }
  if (!readFile)
  {
    EO_FATAL() << "Error: no input specified.";
  }
  if (!generateParser && pluginName != "lean-meta")
  {
    EO_FATAL() << "Error: --no-parser requires --plugin.lean-meta";
  }
  if (!defsFile.empty() && pluginName != "model-smt")
  {
    EO_FATAL() << "Error: --defs requires --plugin.model-smt";
  }
  if (!leanConfigFile.empty() && pluginName != "lean-meta")
  {
    EO_FATAL() << "Error: --lean-config requires --plugin.lean-meta";
  }
  // options are finalized, now initialize the state and the plugin
  Stats stats;
  State s(opts, stats);
  std::unique_ptr<Plugin> plugin;
  if (!pluginName.empty())
  {
    plugin =
        createPlugin(pluginName, s, generateParser, defsFile, leanConfigFile);
    // note the plugin must be set before any file is included, so that it
    // receives callbacks during parsing
    s.setPlugin(plugin.get());
  }
  for (size_t j = 0, nincludes = includes.size(); j < nincludes; j++)
  {
    const std::string& ifile = includes[j].first;
    bool isInclude = includes[j].second;
    // cannot provide reference
    Expr refNf;
    if (!s.includeFile(ifile, isInclude, !isInclude, refNf))
    {
      EO_FATAL() << "Error: cannot include file " << ifile;
    }
  }
  // whether it is a signature is determined by file extension *.eo.
  bool isSignature = (file.size() >= 3 && file.substr(file.size() - 3) == ".eo");
  if (!s.includeFile(file, isSignature))
  {
    EO_FATAL() << "Error: cannot include file " << file;
  }
  if (plugin != nullptr)
  {
    plugin->finalize();
  }
  // exit immediately, which avoids deleting all expressions which can take time
  exit(0);
  return 0;
}
