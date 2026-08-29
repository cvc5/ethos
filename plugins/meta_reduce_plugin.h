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

/** The kind of conjecture emitted by the meta-reduction backends. */
enum class ConjectureType
{
  /** A verification condition, checked by an SMT solver. */
  VC,
  /** A syntax-guided synthesis conjecture. */
  SYGUS
};

/**
 * Base class for the meta-reduction backends (SmtMetaReduce, LeanMetaReduce).
 * It implements the classification of the symbols of a (desugared) Eunoia
 * signature into MetaKind, that is, into the datatypes of the final deep
 * embedding, and provides utilities shared by the backends, e.g. for
 * rendering their template resource files.
 */
class MetaReducePlugin : public StdPlugin
{
 public:
  /** A (tag, replacement) pair used when rendering a resource file. */
  using Replacement = std::pair<std::string, std::string>;

  MetaReducePlugin(State& s, ConjectureType conjType = ConjectureType::VC);
  ~MetaReducePlugin() override;

  /** Notification that name was bound to e; dispatches to finalizeDecl. */
  void bind(const std::string& name, const Expr& e) override;

 protected:
  /** The type of the emitted conjecture (VC or SyGuS), set at construction. */
  ConjectureType optionMetaConjectureType() const;
  /**
   * Get the name of e, or the empty string if e is not atomic. Note this is
   * the name e was bound to, which is not necessarily how e is printed, e.g.
   * a symbol declared as |foo bar| has name "foo bar".
   */
  static std::string getName(const Expr& e);
  /**
   * Is e a constructor of one of the deep embedding datatypes? These are
   * the constants whose names begin with "$emb_".
   */
  static bool isEmbedCons(const Expr& e);
  /**
   * Is oApp an (opaque) application of one of the symbols of the native
   * embedding that carry an SMT-LIB identifier as their first argument,
   * i.e. $native_apply_*, $native_type_* or $native_datatype?
   */
  static bool isSmtApplyApp(const Expr& oApp);
  /**
   * Get the meta-kind associated with the given constructor prefix, e.g.
   * SMT_VALUE for "vsm", or elseKind if the prefix is not registered.
   */
  MetaKind prefixToMetaKind(const std::string& str, MetaKind elseKind) const;
  /**
   * Get the meta-kind of the type typ, or elseKind if typ is not one of the
   * types of the deep embedding. If followFunctionRange is true and typ is
   * a function type, we classify its range instead. Note that eo::requires
   * guards, which may wrap typ or the range of a function type, are ignored.
   */
  MetaKind getTypeMetaKindFor(const Expr& typ,
                              MetaKind elseKind,
                              bool followFunctionRange) const;
  /**
   * Get the meta-kind of the term e, that is, the datatype of the deep
   * embedding that e belongs to. Sets cname to the name e contributes to
   * the final embedding, e.g. the constructor name without its "$emb_<prefix>."
   * wrapper.
   */
  MetaKind getMetaKindFor(const Expr& e, std::string& cname) const;
  /**
   * If typ, or the range of typ if it is a function type, is an application
   * of a $native_embed_* symbol to an SMT-LIB identifier, return that
   * application, otherwise return the null expression. As above, eo::requires
   * guards are ignored.
   */
  static Expr getEmbedTypeApp(const Expr& typ);
  /**
   * Get the name of the embedded datatype carried by a $native_embed_*
   * application, e.g. "SmtRegLan" for ($native_embed_smt "SmtRegLan"). This
   * aborts if app does not have that shape, see getEmbedTypeApp.
   */
  static std::string getEmbedTypeName(const Expr& app);
  /**
   * If e is a lambda defining a $eo_ symbol named name, construct an
   * equivalent single-case program. Sets symbol to a fresh program constant
   * for name and prog to its definition, and returns true if successful.
   */
  bool buildLambdaDefineProgram(const std::string& name,
                                const Expr& e,
                                Expr& symbol,
                                Expr& prog);
  /**
   * Called at the beginning of finalizeDecl for e. Returns true if e has not
   * been finalized yet, and marks it as seen.
   */
  bool beginFinalizeDecl(const Expr& e);
  /** Is app an application of a program constant? */
  static bool isProgramApp(const Expr& app);
  /**
   * Render the template resource file resourcePath by applying the given
   * replacements and write the result to outputPath. If replAll is true,
   * every occurrence of each tag is replaced, otherwise only the first. A tag
   * that does not occur in the template is a no-op, which we warn about since
   * it is always a mistake. What the resource says to whoever edits it is
   * dropped, see dropResourceNotes. Returns the full path of the written
   * file.
   */
  std::string emitResourceFile(const std::string& resourcePath,
                               const std::string& outputPath,
                               const std::vector<Replacement>& replacements,
                               bool replAll = false) const;

  /**
   * Is sname the name of a symbol supplied by the backend's templates? Such
   * symbols are not included in the generated output.
   */
  virtual bool isBuiltinMetaSymbol(const std::string& sname) const = 0;
  /** Process the declaration of constant e in the backend. */
  virtual void finalizeDecl(const Expr& e) = 0;

  /** The null expression. */
  Expr d_null;
  /** Maps $emb_ constructor prefixes (e.g. "vsm") to their meta-kind. */
  std::map<std::string, MetaKind> d_prefixToMetaKind;
  /** Maps names of types of the deep embedding to their meta-kind. */
  std::map<std::string, MetaKind> d_typeToMetaKind;
  /** The declarations processed so far, see beginFinalizeDecl. */
  std::set<Expr> d_declSeen;

 private:
  /** The type of the emitted conjecture, set at construction. */
  ConjectureType d_conjectureType;
  /** Initialize the meta-kind maps shared by all backends. */
  void initializeCommonMetaKinds();
};

}  // namespace ethos

#endif
