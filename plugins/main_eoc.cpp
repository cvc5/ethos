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
 *   ethos-eoc --plugin.model-smt --signature=<file> [--semantics=<file>] <file>
 *   ethos-eoc --plugin.lean-meta --lean-config=<file> [--no-trim-natives] <file>
 *
 * With no --plugin.* argument, it parses the given file like plain ethos.
 * Unlike the plain ethos binary, it requires a file argument (no stdin mode)
 * and does not print a proof checking verdict; a run is successful iff the
 * exit code is 0.
 */

#include <iostream>
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

// Whether key names an option of ethos that ethos-eoc does not take, however
// it was written: --key and --no-key are the same option to setOption, so they
// are the same option here.
bool isUnsupportedOption(const std::string& key)
{
  // This binary compiles a signature rather than checking a proof, so an
  // option about what a proof has to look like has nothing here to act on.
  // Setting it would quietly do nothing, which is worse than saying it is not
  // an option this binary takes.
  return key == "require-proof-of-false";
}

std::unique_ptr<Plugin> createPlugin(const std::string& name,
                                     State& s,
                                     bool generateParser,
                                     const std::string& defsFile,
                                     const std::string& smtDefsFile,
                                     const std::string& leanConfigFile,
                                     bool trimNatives)
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
    return std::make_unique<LeanMetaReduce>(
        s, generateParser, leanConfigFile, trimNatives);
  }
  if (name == "trim-defs")
  {
    return std::make_unique<TrimDefs>(s);
  }
  if (name == "model-smt")
  {
    // With no --signature the plugin reads the signature it defaults to; naming
    // one that is empty would instead fail once the stage runs. With no
    // --semantics it reads the SMT-LIB signature it ships with.
    if (defsFile.empty() && smtDefsFile.empty())
    {
      return std::make_unique<ModelSmt>(s);
    }
    return std::make_unique<ModelSmt>(s, defsFile, smtDefsFile);
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
  std::string smtDefsFile;
  std::string leanConfigFile;
  bool trimNatives = true;
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
    if (arg == "--no-trim-natives")
    {
      // Emit the whole of the native layer rather than the part of it the
      // compilation of the input reaches, which is for reading what was
      // dropped rather than for anything a run publishes.
      trimNatives = false;
      continue;
    }
    if (arg.compare(0, 12, "--semantics=") == 0)
    {
      // The SMT-LIB signature written in the deep embedding, which the input's
      // is written against. The plugin ships with one, so this is what names
      // another; like --signature, it is read by the model-smt plugin alone.
      smtDefsFile = arg.substr(12);
      continue;
    }
    if (arg.compare(0, 12, "--signature=") == 0)
    {
      // The signature of the input written in the deep embedding, which says
      // what each of its symbols means to the model. It is read by the
      // model-smt plugin alone; no stage before that one sees it.
      defsFile = arg.substr(12);
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
    bool isInclude = (arg.compare(0, 10, "--include=") == 0);
    if (isInclude || arg.compare(0, 12, "--reference=") == 0)
    {
      // defer the inclusion until the options are finalized
      size_t first = arg.find_first_of("=");
      std::string ifile = arg.substr(first + 1);
      includes.emplace_back(ifile, isInclude);
      continue;
    }
    // The options of ethos itself, which are what is left that begins with a
    // dash: every option of this binary alone is handled above. One ethos does
    // not have, or has and this binary does not take, is an error here rather
    // than an argument to fall through to, so that it cannot be read as the
    // name of the input file further down.
    if (arg.compare(0, 5, "--no-") == 0 || arg.compare(0, 2, "--") == 0)
    {
      bool val = (arg.compare(0, 5, "--no-") != 0);
      std::string key = arg.substr(val ? 2 : 5);
      if (isUnsupportedOption(key))
      {
        EO_FATAL() << "Error: " << arg << " is not supported by ethos-eoc";
      }
      if (!opts.setOption(key, val))
      {
        EO_FATAL() << "Error: unrecognized option " << arg;
      }
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
    else if (arg.compare(0, 1, "-") == 0)
    {
      EO_FATAL() << "Error: unrecognized option " << arg;
    }
    else if (!readFile)
    {
      file = arg;
      readFile = true;
    }
    else
    {
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
  if (!smtDefsFile.empty() && pluginName != "model-smt")
  {
    EO_FATAL() << "Error: --semantics requires --plugin.model-smt";
  }
  if (!defsFile.empty() && pluginName != "model-smt")
  {
    EO_FATAL() << "Error: --signature requires --plugin.model-smt";
  }
  if (!leanConfigFile.empty() && pluginName != "lean-meta")
  {
    EO_FATAL() << "Error: --lean-config requires --plugin.lean-meta";
  }
  if (!trimNatives && pluginName != "lean-meta")
  {
    EO_FATAL() << "Error: --no-trim-natives requires --plugin.lean-meta";
  }
  // options are finalized, now initialize the state and the plugin
  Stats stats;
  State s(opts, stats);
  std::unique_ptr<Plugin> plugin;
  if (!pluginName.empty())
  {
    plugin =
        createPlugin(pluginName, s, generateParser, defsFile, smtDefsFile,
                     leanConfigFile, trimNatives);
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
  if (opts.d_stats)
  {
    std::cout << stats.toString(s, opts.d_statsCompact, opts.d_statsAll);
  }
  // exit immediately, which avoids deleting all expressions which can take time
  exit(0);
  return 0;
}
