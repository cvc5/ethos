/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "model_smt.h"

#include <fstream>
#include <sstream>
#include <string>
#include <type_traits>

#include "../utils.h"
#include "state.h"

namespace ethos {

static_assert(std::is_constructible<ModelSmt, State&>::value,
              "ModelSmt must support the generic plugin factory");

ModelSmt::ModelSmt(State& s) : ModelSmt(s, "")
{
  // The plugin has no signature of its own to fall back on: which input is
  // being compiled is not its business, so the signature of that input is
  // given to it with --signature and loadDefs is what says so when it is not. The
  // SMT-LIB signature is the one exception, since it is the target.
}

ModelSmt::ModelSmt(State& s,
                   const std::string& defsFile,
                   const std::string& smtDefsFile)
    : StdPlugin(s), d_defsFile(defsFile), d_smtDefsFile(smtDefsFile)
{
  // What each symbol of a signature means to the model is said by the
  // signatures written in the deep embedding rather than here, see loadDefs
  // and tools/eoc/out/smt_defs.eo.
}

ModelSmt::~ModelSmt() {}

void ModelSmt::bind(const std::string& name, const Expr& e)
{
  if (e.getKind() != Kind::CONST)
  {
    return;
  }
  d_declSeen.emplace_back(name, e);
}

void ModelSmt::finalizeDecl(const std::string& name)
{
  if (d_defsCovered.count(name) != 0)
  {
    // a symbol one of the signatures written in the deep embedding is of,
    // whose block is what says its meaning, see loadDefs
    return;
  }
  // A name of the desugar stage or of a signature helper rather than a symbol
  // a proof may write, so no model has to say anything about it.
  if (name.compare(0, 1, "$") == 0 || name.compare(0, 2, "@@") == 0)
  {
    return;
  }
  // This assertion is critical for soundness: if we do not know how to
  // interpret the symbol, we cannot claim this verification condition
  // accurately models SMT-LIB semantics.
  EO_FATAL() << "ERROR: no model semantics found for " << name;
}

void ModelSmt::loadDefs()
{
  // The SMT-LIB signature is the target of the compilation, so the plugin
  // ships with one and reads that where it was given no other; --semantics is
  // what gives it another, the way --signature gives it the input's.
  const std::string smtDefs =
      d_smtDefsFile.empty() ? getResourcePath("tools/eoc/out/smt_defs.eo")
                            : d_smtDefsFile;
  if (!d_smtDefs.read(smtDefs))
  {
    EO_FATAL() << "ModelSmt: could not read the SMT-LIB signature written in"
                  " the deep embedding at "
               << smtDefs;
  }
  if (d_defsFile.empty())
  {
    EO_FATAL() << "ModelSmt: no signature of the input was given; pass --signature,"
                  " see tools/eoc/driver.py";
  }
  if (!d_inputDefs.read(d_defsFile))
  {
    EO_FATAL() << "ModelSmt: could not read the signature of the input at "
               << d_defsFile;
  }
  // The blocks the input needs are the ones of a symbol it declares, together
  // with the ones those name, see DefsFile::select.
  std::set<std::string> syms;
  for (const std::pair<std::string, Expr>& d : d_declSeen)
  {
    syms.insert(d.first);
  }
  // The transformation of a symbol names the constructor of what it denotes,
  // which is a block of the other file, so what the one needs of the other is
  // taken as well.
  std::vector<const DefsBlock*> in = d_inputDefs.select(syms);
  std::vector<const DefsBlock*> blocks =
      d_smtDefs.select(syms, d_inputDefs.externalUses(in));
  blocks.insert(blocks.end(), in.begin(), in.end());
  // A program has to be defined before it is called, which the order of the
  // files is what gives; a constructor and a case have no such order, since a
  // case matches a head of its own and a constructor names nothing of another
  // symbol. So the two are emitted in the order the *input* declares its
  // symbols, which is the order the generated file has had them in, and a
  // block of a symbol the input does not declare goes just before the one that
  // needs it, e.g. the constructor of uneg before the case for the overloaded
  // minus that names it.
  std::vector<std::string> declarations;
  for (const std::pair<std::string, Expr>& d : d_declSeen)
  {
    declarations.push_back(d.first);
  }
  std::vector<const DefsBlock*> byDecl =
      orderByDeclarations(blocks, declarations);
  for (const DefsBlock* b : byDecl)
  {
    // A block that says nothing about the model, e.g. one that only gives the
    // nil of an n-ary symbol, leaves that symbol to be compiled as any other.
    if (!b->d_cons.empty() || !b->d_typeofCases.empty()
        || !b->d_evalCases.empty() || !b->d_transCases.empty()
        || !b->d_transTypeCases.empty())
    {
      d_defsCovered.insert(b->d_sym);
    }
    for (const std::string& f : b->d_cons)
    {
      d_smtTerms << f << std::endl;
    }
    for (const std::string& c : b->d_typeofCases)
    {
      d_smtTypeof << "  " << c << std::endl;
    }
    for (const std::string& c : b->d_evalCases)
    {
      d_eval << "  " << c << std::endl;
    }
    for (const std::string& c : b->d_transCases)
    {
      d_eoToSmt << "  " << c << std::endl;
    }
    for (const std::string& c : b->d_transTypeCases)
    {
      d_eoToSmtType << "  " << c << std::endl;
    }
  }
  // The types are the embedding's own -- every block of one is kept, whatever
  // the input declares -- so they stand in the order the configuration gives
  // them rather than in the order a calculus declares its own. What is derived
  // from that order is then the same in every generated package however few
  // rules it was compiled for, e.g. the key a value is ordered by, see
  // typeKey in the generated SmtValueOrder.
  for (const DefsBlock* b : blocks)
  {
    for (const std::string& f : b->d_typeCons)
    {
      d_smtTypes << f << std::endl;
    }
    for (const std::string& c : b->d_typeWfCases)
    {
      d_typeWf << "  " << c << std::endl;
    }
    for (const std::string& c : b->d_typeBoundedCases)
    {
      d_typeBounded << "  " << c << std::endl;
    }
    for (const std::string& c : b->d_typeDefaultCases)
    {
      d_typeDefault << "  " << c << std::endl;
    }
  }
  // The programs follow the same order, which they may because each evaluator
  // is forward declared above; a method that is not, having been written
  // beside the symbol it belongs to, is ordered by the file it comes from,
  // which is what puts it before whatever calls it.
  for (const DefsBlock* b : byDecl)
  {
    for (const std::string& f : b->d_typeofAux)
    {
      d_smtTypeofAux << f << std::endl;
    }
    for (const std::string& f : b->d_evalFwd)
    {
      d_modelEvalProgsFwd << f << std::endl;
    }
    for (const std::string& f : b->d_evalProgs)
    {
      d_modelEvalProgs << f << std::endl;
    }
    for (const std::string& f : b->d_eoAux)
    {
      d_eoToSmtAux << f << std::endl;
    }
    for (const std::string& f : b->d_desugarAux)
    {
      d_desugarAux << f << std::endl;
    }
  }
}

void ModelSmt::finalize()
{
  // What each symbol of the signatures written in the deep embedding says,
  // which this plugin copies rather than deriving, see loadDefs.
  loadDefs();
  for (std::pair<std::string, Expr>& d : d_declSeen)
  {
    finalizeDecl(d.first);
  }
  // Each placeholder is commented out in the template, which is what lets that
  // template be parsed on its own, see plugins/model_smt/model_smt.eo. The
  // comment is part of what a substitution replaces, so that the generated
  // content takes the whole line.
  auto replacePlaceholder = [](std::string& txt,
                               const std::string& tag,
                               const std::string& replacement) {
    const std::string guarded = ";" + tag;
    auto pos = txt.find(guarded);
    if (pos == std::string::npos)
    {
      EO_FATAL() << "ModelSmt: template is missing placeholder " << tag;
    }
    txt.replace(pos, guarded.length(), replacement);
  };

  // note that the deep embedding is *not* re-incorporated into
  // the final input to smt-meta.

  // now, go back and compile *.eo for the proof rules
  const std::string templatePath =
      getResourcePath("plugins/model_smt/model_smt.eo");
  std::ifstream ins(templatePath);
  if (!ins.is_open())
  {
    EO_FATAL() << "ModelSmt: failed to open resource " << templatePath;
  }
  std::ostringstream sss;
  sss << ins.rdbuf();
  if (ins.bad())
  {
    EO_FATAL() << "ModelSmt: failed to read resource " << templatePath;
  }
  std::string finalSmt = sss.str();
  // plug in the evaluation cases handled by this plugin
  replacePlaceholder(finalSmt, "$SMT_EVAL_CASES$", d_eval.str());
  replacePlaceholder(
      finalSmt, "$SMT_EVAL_PROGS_FWD_DECL$", d_modelEvalProgsFwd.str());
  replacePlaceholder(finalSmt, "$SMT_EVAL_PROGS$", d_modelEvalProgs.str());
  replacePlaceholder(finalSmt, "$EO_TO_SMT_AUX$", d_eoToSmtAux.str());
  replacePlaceholder(finalSmt, "$EO_DESUGAR_AUX$", d_desugarAux.str());
  replacePlaceholder(finalSmt, "$EO_TO_SMT_CASES$", d_eoToSmt.str());
  replacePlaceholder(finalSmt, "$EO_TO_SMT_TYPE_CASES$", d_eoToSmtType.str());
  replacePlaceholder(finalSmt, "$SMT_TERM_CONSTRUCTORS$", d_smtTerms.str());
  replacePlaceholder(finalSmt, "$SMT_TYPE_CONSTRUCTORS$", d_smtTypes.str());
  replacePlaceholder(finalSmt, "$SMT_TYPE_WF_CASES$", d_typeWf.str());
  replacePlaceholder(finalSmt, "$SMT_TYPE_BOUNDED_CASES$", d_typeBounded.str());
  replacePlaceholder(finalSmt, "$SMT_TYPE_DEFAULT_CASES$", d_typeDefault.str());
  replacePlaceholder(finalSmt, "$SMT_TYPEOF_CASES$", d_smtTypeof.str());
  replacePlaceholder(finalSmt, "$SMT_TYPEOF_AUX$", d_smtTypeofAux.str());
  if (finalSmt.find("$eoc_") != std::string::npos)
  {
    EO_FATAL() << "ModelSmt: generated output contains an unexpanded $eoc_ "
                  "name";
  }

  std::string outPath = getOutputPath("plugins/model_smt/model_smt_gen.eo");
  std::ofstream oute(outPath);
  if (!oute.is_open())
  {
    EO_FATAL() << "ModelSmt: failed to open output " << outPath;
  }
  oute << finalSmt;
  oute.close();
  if (!oute)
  {
    EO_FATAL() << "ModelSmt: failed to write output " << outPath;
  }
}

}  // namespace ethos
