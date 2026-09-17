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

/** The executable checker fragment of the Isabelle/HOL meta backend.
 *
 * Like lean-meta, this consumes the desugar embedding. Programs return an
 * option and take a recursion budget: None means exhaustion, whereas an EO
 * pattern failure returns Some Term_Stuck. No termination axioms are needed.
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
  static std::string identifier(const std::string& name);
  std::string type(const Expr& t) const;
  std::string constructor(const Expr& e) const;
  std::string atom(const Expr& e) const;
  std::string native(const std::string& name,
                     const std::vector<std::string>& args) const;
  std::string call(const std::string& name,
                   const std::vector<std::string>& args);
  std::string term(const Expr& e);
  std::string pattern(const Expr& e,
                      std::set<Expr>& bound,
                      std::vector<std::string>& guards);
  std::string equations(const Program& p);
  std::map<std::string, std::vector<std::string>> d_datatypes;
  std::map<std::string, std::set<std::string>> d_datatypeDeps;
  std::map<std::string, Program> d_programs;
  std::map<std::string, std::set<std::string>> d_calls;
  std::set<std::string> d_rules;
  std::string d_current;
  size_t d_fresh = 0;
};

}  // namespace ethos

#endif
