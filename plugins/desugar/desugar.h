/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef DESUGAR_H
#define DESUGAR_H

#include <map>
#include <set>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

#include "../std_plugin.h"
#include "desugar_checker.h"

namespace ethos {

class State;
class TypeChecker;

/**
 * Plugin that parses an arbitrary Eunoia input into the "desugared" Eunoia
 * core.
 *
 * The desugar stage is an EO-to-EO compilation pass.  It records declarations,
 * program definitions, proof rules, datatype metadata, literal type rules, and
 * constructor attributes as the parser reports them, then emits a generated
 * `eo_desugar_gen.eo` file during finalize().  The generated file combines the
 * static desugaring template with auto-generated cases for:
 * - user declarations and programs,
 * - the definitions of the input, preserved under the parse definition prefix
 *   for the generated proof parser (see getParseDefPrefix),
 * - overloaded symbols and opaque/ambiguous applications,
 * - list nil and list-nil recognition,
 * - datatype constructor and selector reflection,
 * - the approximate `eo::typeof` rules used by later stages, and
 * - optional proof-rule checker or verification-condition programs.
 *
 * This pass intentionally keeps the output inside Eunoia.  Later plugins, such
 * as model_smt and the SMT/Lean meta encoders, consume the smaller core
 * language produced here and provide the remaining model semantics.
 */
class Desugar : public StdPlugin
{
 public:
  /** Construct the desugaring plugin and initialize builtin helper symbols. */
  Desugar(State& s, bool genVcs = false);
  /** Destroy the desugaring plugin. */
  ~Desugar();
  /** Remember supported macro definitions for processing during finalize(). */
  void define(const std::string& name, const Expr& e) override;
  /** Remember constants and proof rules in declaration order. */
  void bind(const std::string& name, const Expr& e) override;
  /** Record constructor or declaration attributes supplied by the parser. */
  void markConstructorKind(const Expr& v, Attr a, const Expr& cons) override;
  /** Remember a program definition or forward declaration. */
  void defineProgram(const Expr& v, const Expr& prog) override;
  /** Generate the desugared EO output and supporting resource files. */
  void finalize() override;
  /** Consume echo commands used as dependency markers by later tooling. */
  bool echo(const std::string& msg) override;
  /** Set and emit the desugared type rule for literal kind k. */
  void setLiteralTypeRule(Kind k, const Expr& t) override;

  /** Print an expression after applying overload and proof sanitization. */
  void printTerm(const Expr& e, std::ostream& os);

 private:
  /** Print the emitted name for e, assigning overload suffixes as needed. */
  void printName(const Expr& e, std::ostream& os);
  /** Print a dependency-ordered parameter list for vars. */
  void printParamList(const std::vector<Expr>& vars,
                      std::ostream& os,
                      bool useImplicit,
                      bool isOpaque = false);
  /** Print vars while sharing accumulated parameter and visited state. */
  void printParamList(const std::vector<Expr>& vars,
                      std::ostream& os,
                      std::vector<Expr>& params,
                      std::map<Expr, bool>& visited,
                      bool useImplicit,
                      bool isOpaque = false);
  /** Collect vars and type dependencies in a stable declaration order. */
  void getParamList(const std::vector<Expr>& vars,
                    std::vector<Expr>& params,
                    std::map<Expr, bool>& visited);
  /** Emit the final parameter entries with implicit or opaque annotations. */
  void finalizeParamList(std::ostream& os,
                         const std::vector<Expr>& params,
                         bool useImplicit,
                         const std::vector<Expr>& nimplicit,
                         bool isOpaque = false,
                         size_t startIndex = 0);
  /** Emit one desugared program definition or forward declaration. */
  void finalizeProgram(const Expr& v, const Expr& prog, std::ostream& os);
  /** Emit the preserved definition of name as a parse definition. */
  void finalizeDefinition(const std::string& name, const Expr& t);
  /** Emit a constant declaration and all derived helper cases for it. */
  void finalizeDeclaration(const Expr& t, std::ostream& os);
  /** Emit checker or verification-condition artifacts for a proof rule. */
  void finalizeRule(const Expr& v);
  /**
   * Emit datatype reflection cases for datatypes, constructors, and selectors.
   */
  void finalizeDatatype(const Expr& d, Attr a, const Expr& attrCons);
  /**
   * Emit is_closed cases for the binder e.
   */
  void finalizeBinder(const Expr& e, const Expr& attrCons);
  /** Sanitize an expression using the default overload-renaming map. */
  Expr mkSanitize(const Expr& t);
  /** Sanitize an expression while reusing or extending a caller map. */
  Expr mkSanitize(const Expr& t, std::map<Expr, Expr>& visited);
  /** Build a model-satisfaction requirement used by VC generation. */
  Expr mkRequiresModelSat(const Expr& m,
                          bool tgt,
                          const Expr& test,
                          const Expr& ret);
  /** Build an evaluation requirement that compares t1 and t2 before ret. */
  Expr mkRequiresEq(const Expr& t1,
                    const Expr& t2,
                    const Expr& ret,
                    bool neg = false);
  /** Return the recorded parser attribute for e, or Attr::NONE. */
  Attr getAttribute(const Expr& e);
  /** Return whether a source symbol should be omitted from generated output. */
  bool isExcluded(const Expr& e, Kind k) const;
  /**
   * The `$emb_UOp<n>` constructors for the index arities of d_indexArities,
   * as the text of the $EO_UOP_DECLS$ hole of the native embedding.
   */
  std::string printUopDecls() const;
  /**
   * The `$eo_is_closed_rec` cases for the index arities of d_indexArities,
   * as the text of the $EO_IS_CLOSED_UOP_CASES$ hole of the template.
   */
  std::string printIsClosedUopCases() const;

  /** Declarations and definitions in the order seen by the plugin. */
  std::vector<std::pair<Expr, Kind>> d_declSeen;
  /** The last definition given for each defined name. */
  std::map<std::string, Expr> d_defineLast;
  /** Parser-supplied attributes and their constructor payloads. */
  std::map<Expr, std::pair<Attr, Expr>> d_attrDecl;
  /** Declarations already emitted, used to avoid duplicate output. */
  std::set<Expr> d_declProcessed;
  /** Number of same-printed names already assigned for overload handling. */
  std::map<std::string, size_t> d_overloadCount;
  /** Assigned overload index for each expression that needs a unique name. */
  std::map<Expr, size_t> d_overloadId;
  /** Replacement map used when printing sanitized overloaded terms. */
  std::map<Expr, Expr> d_overloadSanVisited;
  /** Null expression placeholder used by iterative expression rewrites. */
  Expr d_null;
  /** Common list nil symbol. */
  Expr d_listNil;
  /** Common list cons symbol. */
  Expr d_listCons;
  /** Common list type symbol. */
  Expr d_listType;
  /** Common Bool type symbol. */
  Expr d_boolType;
  /** Common true literal. */
  Expr d_true;
  /** Whether proof rules should be emitted as VC targets. */
  bool d_genVcs;
  /** Whether the executable checker should be emitted. */
  bool d_genChecker;
  /** Source proof-rule names explicitly omitted from generated output. */
  std::set<std::string> d_excludedRules;
  /** Source program names explicitly omitted from generated output. */
  std::set<std::string> d_excludedMethods;
  /** Source theory-symbol names explicitly omitted from generated output. */
  std::set<std::string> d_excludedSymbols;

  /** Literal kinds whose type rules have already been emitted. */
  std::unordered_set<Kind> d_ltKindProcessed;
  /** Declarations already emitted for literal type dependencies. */
  std::set<Expr> d_ltDeclProcessed;
  /** Generated declarations for literal type symbols. */
  std::stringstream d_litTypeDecl;
  /** Generated programs that compute literal types. */
  std::stringstream d_litTypeProg;
  /** Generated user declarations and program definitions. */
  std::stringstream d_defs;
  /** Generated `$eo_is_list_nil` cases. */
  std::stringstream d_eoIsListNil;
  /** Generated programs for non-ground `$eo_nil` cases. */
  std::stringstream d_eoNilNground;
  /** Generated `$eo_nil` cases. */
  std::stringstream d_eoNil;
  /**
   * Parser-only metadata preserved for the Lean backend. Desugaring removes
   * constructor attributes from emitted declarations, so this records the
   * original surface syntax before that information is lost.
   */
  std::stringstream d_leanParserMetadata;
  /** Generated `$eo_typeof` cases. */
  std::stringstream d_eoTypeof;
  /** Generated `$eo_is_closed` cases. */
  std::stringstream d_eoIsClosed;
  /**
   * The index arities the signature uses, i.e. the n for which it declares an
   * operator with n opaque arguments. The Lean backend represents such an
   * operator as `UserOp<n>`, so this is the ladder of index arities the
   * compiled calculus actually has, and $eo_is_closed_rec gets a case for
   * each and no others: a case names $eot_uop<n>, and naming it is what keeps
   * $emb_UOp<n> reachable through the trimming, which is what gives Term a
   * UOp<n> constructor. An arity nothing declares is therefore an arity that
   * reaches neither the embedding nor Term.
   *
   * A declaration the trimming later drops leaves its arity here, so this may
   * name one more arity than the backend emits a constructor for. That way
   * round is a dead case; the other way round would be a case that names a
   * constructor the embedding does not have.
   */
  std::set<size_t> d_indexArities;
  /** Generated helper programs for non-ground `$eo_typeof` cases. */
  std::stringstream d_eoTypeofNGround;
  /** Generated parameter binders for datatype-constructor reflection. */
  std::stringstream d_eoDtConsParam;
  /** Generated datatype-constructor reflection cases. */
  std::stringstream d_eoDtCons;
  /** Generated datatype-selector reflection cases. */
  std::stringstream d_eoDtSel;
  /** Generated verification-condition programs and markers. */
  std::stringstream d_eoVc;

  /** `$eo_model_sat` helper symbol used in generated VCs. */
  Expr d_peoModelSat;
  /** `$eo_model_unsat` helper symbol used in strict generated VCs. */
  Expr d_peoModelUnsat;
  /** `$eo_requires_eq` helper symbol used in generated requirements. */
  Expr d_peoRequiresEq;
  /** Number of datatype-constructor type parameters already declared. */
  size_t d_eoDtConsParamCount;
  /** `$eo_pf` helper symbol used to turn proof nodes into applications. */
  Expr d_peoPf;
  /** Helper responsible for desugaring the executable checker. */
  DesugarChecker d_dchecker;

  //----- For canonizing type rules
  /** Canonicalize type variables before comparing generated type programs. */
  Expr mkCanonize(const Expr& t);
  /** Per-type reusable canonical variables. */
  std::map<Expr, std::vector<Expr>> d_vars;
  /** Generated typeof helper program name for each canonicalized type. */
  std::map<Expr, std::string> d_canonTypeProgName;
};

}  // namespace ethos

#endif /* DESUGAR_H */
