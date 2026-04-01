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

#include "smt_meta/utils.h"
#include "std_plugin.h"

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
  std::string emitResourceFile(
      const std::string& resourcePath,
      const std::string& outputPath,
      const std::vector<Replacement>& replacements) const;

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
