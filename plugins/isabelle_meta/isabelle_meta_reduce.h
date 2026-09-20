/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#ifndef PLUGIN_ISABELLE_META_REDUCE_H
#define PLUGIN_ISABELLE_META_REDUCE_H

#include "../meta_reduce_plugin.h"

namespace ethos {

/** The checker and logical-model passes of the Isabelle/HOL meta backend.
 *
 * Like lean-meta, this consumes the desugar embedding. Programs return an
 * option and take a recursion budget: None means exhaustion, whereas an EO
 * pattern failure returns Some Term_Stuck. The separate model pass imports
 * the checker's constructors and generates fuel-free definitions whose
 * coverage and termination must be proved in HOL. Neither pass adds axioms.
 */
class IsabelleMetaReduce : public MetaReducePlugin
{
 public:
  explicit IsabelleMetaReduce(State& s);
  void defineProgram(const Expr& v, const Expr& prog) override;
  void define(const std::string& name, const Expr& e) override;
  bool echo(const std::string& msg) override;
  void finalize() override;

 private:
  struct Program
  {
    Expr symbol;
    Expr body;
    bool macro = false;
  };
  bool isBuiltinMetaSymbol(const std::string& name) const override;
  void finalizeDecl(const Expr& e) override;
  std::string identifier(const std::string& name, const std::string& prefix);
  std::string type(const Expr& t) const;
  std::string constructor(const Expr& e);
  size_t indexedArity(const Expr& e) const;
  bool isUserOperator(const Expr& e) const;
  std::string atom(const Expr& e);
  std::string native(const std::string& name,
                     const std::vector<std::string>& args) const;
  std::string call(const std::string& name,
                   const std::vector<std::string>& args);
  std::string term(const Expr& e);
  std::string pattern(const Expr& e,
                      std::set<Expr>& bound,
                      std::vector<std::string>& guards);
  std::string programBody(const Program& p);
  void finalizeBindings();
  void finalizeModel();
  std::string modelTerm(const Expr& e);
  std::string modelBody(const Program& p);
  std::string modelCall(const std::string& name,
                        const std::vector<std::string>& args);
  bool d_model = false;
  std::map<std::string, std::string> d_importedConstructors;
  std::set<std::string> d_importedTypes;
  struct ParserOp
  {
    std::string surface, generated, attr, connector;
    size_t indices = 0, arguments = 0;
  };
  void finalizeParser();
  std::string parserTerm(const Expr& e);
  std::vector<ParserOp> d_parserOps;
  std::vector<std::pair<std::string, std::string>> d_parserRules;
  std::vector<std::pair<std::string, Expr>> d_parseDefs;
  std::map<std::string, Expr> d_parserSymbols;
  std::map<std::string, std::vector<std::string>> d_datatypes;
  std::map<std::string, std::set<std::string>> d_datatypeDeps;
  std::map<std::string, Program> d_programs;
  std::map<std::string, std::set<std::string>> d_calls;
  std::set<std::string> d_rules;
  std::map<std::string, std::string> d_operatorAliases;
  // Allocate names separately for programs, variables, and each constructor
  // prefix. References reuse the allocation even when readable stems collide.
  std::map<std::string, std::map<std::string, std::string>> d_identifiers;
  std::map<std::string, std::set<std::string>> d_usedIdentifiers;
  std::string d_current;
  size_t d_fresh = 0;
};

}  // namespace ethos

#endif
