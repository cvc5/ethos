/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef PLUGIN_MODEL_SMT_H
#define PLUGIN_MODEL_SMT_H

#include <map>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <unordered_set>
#include <vector>

#include "../std_plugin.h"
#include "defs_reader.h"

namespace ethos {

/**
 * Plugin that generates the EO layer for SMT-LIB model semantics.
 *
 * It consumes the desugared EO signature and emits `model_smt_gen.eo`, which
 * defines the model-evaluation machinery the SMT and Lean meta encoders use:
 * the type language, the value language, and what each symbol of the input
 * denotes in them.
 *
 * What every symbol *means* to the model is not stated here. It is stated by
 * two signatures written directly in the deep embedding: the SMT-LIB one,
 * plugins/model_smt/smt_defs.eo, which is the target and so is fixed, and the
 * one of the input, which is supplied at construction (the bundled CPC
 * signature by default). Each is a sequence of blocks, one per symbol, giving
 * the constructor of the embedding for it, the cases it contributes to
 * `$smtx_typeof`, `$smtx_model_eval`, `$eo_to_smt` and `$eo_to_smt_type`, and
 * the programs those cases call. The plugin algorithms contain no per-symbol
 * model semantics: they take the blocks the input needs, put what each says
 * where it belongs in the template, and check that nothing was left without a
 * meaning.
 *
 * So the work is:
 * - bind records what the input declares, in the order it declares it;
 * - loadDefs reads the two signatures, selects the blocks of the symbols the
 *   input declares together with every block those name, and fills the streams
 *   below from them;
 * - finalizeDecl checks each declared symbol is covered, is internal, or is an
 *   error, which is what keeps a verification condition from claiming to model
 *   a symbol it says nothing about;
 * - finalize substitutes the streams into plugins/model_smt/model_smt.eo.
 *
 * A constructor and a case are emitted in the order the input declares its
 * symbols, since a case matches a head of its own and a constructor names
 * nothing of another symbol. A program is emitted in that order as well, which
 * it may because each evaluator is forward declared.
 */
class ModelSmt : public StdPlugin
{
 public:
  /** Construct the plugin with the bundled CPC input signature. */
  ModelSmt(State& s);
  /**
   * Construct the plugin. defsFile is an absolute or working-directory-relative
   * path to the signature of the *input* written in the deep embedding, which
   * says what each of its symbols means to the model; the SMT-LIB signature it
   * is written against is fixed, being the target rather than a matter of the
   * input. See loadDefs.
   */
  ModelSmt(State& s, const std::string& defsFile);
  /** Destroy the model_smt plugin. */
  ~ModelSmt();
  /** Remember constant declarations for model-semantics generation. */
  void bind(const std::string& name, const Expr& e) override;
  /** Emit the generated EO file containing SMT-LIB model semantics. */
  void finalize() override;

 private:
  /**
   * Read the signatures written directly in the deep embedding, take the
   * blocks the input needs, and put what each says where it belongs. A symbol
   * a block is of is one this plugin then says nothing about itself.
   */
  void loadDefs();
  /** The signature of the input written in the deep embedding. */
  std::string d_defsFile;
  /** The blocks of each file, and the symbols they cover. */
  DefsFile d_smtDefs;
  DefsFile d_inputDefs;
  std::set<std::string> d_defsCovered;

  /**
   * Check that the symbol named name, which the input declares, is one the
   * signatures cover or one no model needs; a symbol that is neither is an
   * error rather than a term the model would say nothing about.
   */
  void finalizeDecl(const std::string& name);
  /** Forward declarations for SMT-LIB model-evaluation helper programs. */
  std::stringstream d_modelEvalProgsFwd;
  /** Auxiliary programs for SMT-LIB model evaluation. */
  std::stringstream d_modelEvalProgs;
  /** SMT-LIB model evaluation cases */
  std::stringstream d_eval;
  /** Generated `$eo_to_smt` conversion cases. */
  std::stringstream d_eoToSmt;
  /** Generated `$eo_to_smt_type` conversion cases. */
  std::stringstream d_eoToSmtType;
  /** Auxiliary definitions used by EO-to-SMT conversion. */
  std::stringstream d_eoToSmtAux;
  /** Generated SMT term constructor declarations. */
  std::stringstream d_smtTerms;
  /** Generated SMT type rules for terms. */
  std::stringstream d_smtTypeof;
  /** Auxiliary definitions used by SMT type rules. */
  std::stringstream d_smtTypeofAux;
  /** Extra desugar helper definitions required by model_smt. */
  std::stringstream d_desugarAux;
  /** Constant declarations in parser order. */
  std::vector<std::pair<std::string, Expr>> d_declSeen;
};

}  // namespace ethos

#endif
