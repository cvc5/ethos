/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef PLUGIN_META_REDUCE_PLUGIN_H
#define PLUGIN_META_REDUCE_PLUGIN_H

#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "std_plugin.h"
#include "utils.h"

namespace ethos {

class MetaReducePlugin : public StdPlugin
{
 public:
  using Replacement = std::pair<std::string, std::string>;

  MetaReducePlugin(State& s);
  ~MetaReducePlugin() override;

  void bind(const std::string& name, const Expr& e) override;

 protected:
  static std::string getName(const Expr& e);
  static bool isEmbedCons(const Expr& e);
  static bool isSmtApplyApp(const Expr& oApp);
  /**
   * Return true if sname is one of the operators that embed a target-language
   * type, i.e. $native_type_N or $native_datatype. The string argument of
   * these operators is the name of the type in the target, used verbatim by
   * every backend, e.g. ($native_type_0 "native_Int") is native_Int and
   * ($native_type_0 "SmtRegLan") is SmtRegLan. This is unlike
   * $native_apply_N, whose string is an SMT-LIB operator name that the Lean
   * backend prefixes with native_ and the SMT2 backend uses bare.
   */
  static bool isNativeTypeOp(const std::string& sname);
  MetaKind prefixToMetaKind(const std::string& str,
                            MetaKind elseKind = MetaKind::EUNOIA) const;
  MetaKind getTypeMetaKindFor(const Expr& typ,
                              MetaKind elseKind,
                              bool followFunctionRange) const;
  MetaKind getMetaKindFor(const Expr& e, std::string& cname) const;
  bool buildLambdaDefineProgram(const std::string& name,
                                const Expr& e,
                                Expr& symbol,
                                Expr& prog);
  bool beginFinalizeDecl(const Expr& e);
  static bool isProgramApp(const Expr& app);
  std::string emitResourceFile(const std::string& resourcePath,
                               const std::string& outputPath,
                               const std::vector<Replacement>& replacements,
                               bool replAll = false) const;

  virtual bool isBuiltinMetaSymbol(const std::string& sname) const = 0;
  virtual void finalizeDecl(const Expr& e) = 0;

  Expr d_null;
  std::map<std::string, MetaKind> d_prefixToMetaKind;
  std::map<std::string, MetaKind> d_typeToMetaKind;
  std::set<Expr> d_declSeen;

 private:
  void initializeCommonMetaKinds();
};

}  // namespace ethos

#endif
