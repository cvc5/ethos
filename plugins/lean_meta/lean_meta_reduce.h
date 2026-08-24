/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef PLUGIN_LEAN_META_REDUCE_H
#define PLUGIN_LEAN_META_REDUCE_H

#include <map>
#include <set>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

#include "../meta_reduce_plugin.h"

namespace ethos {

class State;
class TypeChecker;

/**
 * Plugin that lowers generated EO into a Lean meta-theory file.
 *
 * The Lean meta-reduction stage consumes the desugared/model_smt EO layer and
 * emits Lean definitions for the deep embedding used by proof-rule checking:
 * Eunoia terms and proofs, SMT terms/types/values, checker commands, rules,
 * and the generated programs that connect them.  It follows the naming
 * conventions introduced by desugar and model_smt to classify expressions by
 * `MetaKind`, then prints each EO expression as a Lean term of the
 * corresponding embedded datatype.
 *
 * This stage is the Lean analogue of smt_meta_reduce: instead of producing an
 * SMT-LIB conjecture, it writes Lean definitions, specifications, checker
 * infrastructure, and lemmas that Lean can typecheck and prove terminating.
 */
class LeanMetaReduce : public MetaReducePlugin
{
 public:
  /**
   * Construct the Lean meta reducer and its meta-kind tables.
   *
   * If generateParser is false, omit the signature-specific Logos parser
   * configuration while still emitting every other Lean artifact.
   */
  LeanMetaReduce(State& s,
                 bool generateParser = true,
                 const std::string& configFile = "");
  /** Destroy the Lean meta reducer. */
  ~LeanMetaReduce() override;
  /** Remember a program definition for later Lean emission. */
  void defineProgram(const Expr& v, const Expr& prog) override;
  /** Convert supported define commands into program definitions. */
  void define(const std::string& name, const Expr& e) override;
  /** Emit the generated Lean meta-theory file. */
  void finalize() override;
  /** Interpret Lean-meta control echo commands. */
  bool echo(const std::string& msg) override;

  /** Print the Lean type corresponding to EO type t. */
  bool printMetaType(const Expr& t,
                     std::ostream& os,
                     MetaKind tctx = MetaKind::NONE) const;
  /** Print the Lean type name corresponding to a meta-kind. */
  bool printMetaTypeKind(MetaKind k, std::ostream& os) const;
  /**
   * Print the case of the ordering-key method for a constructor of one of the
   * deeply embedded datatypes, which is used to generate SmtValueOrder. The
   * case maps the constructor named cname, whose index in its datatype is tag
   * and whose argument types (as printed by printMetaType) are argTypes, to
   * (node tag [k1 x1, ..., kn xn]), where ki is the key method for the i^th
   * argument type.
   * @param cname The (already cleaned) name of the constructor.
   * @param argTypes The printed Lean types of its arguments.
   * @param tag The index of the constructor in its datatype.
   * @param os The output stream.
   */
  void printOrderKeyCase(const std::string& cname,
                         const std::vector<std::string>& argTypes,
                         size_t tag,
                         std::ostream& os) const;
  /** Return the name of the ordering-key method for Lean type t, if any. */
  static std::string getOrderKeyMethod(const std::string& t);
  using MetaReducePlugin::getName;
  using MetaReducePlugin::isEmbedCons;
  /**
   * Return the "meta-kind" of a type typ, based on its naming convention
   * introduced in the model_smt layer. In other words, we return the datatype
   * that typ represents if applicable, SMT_BUILTIN if typ refers to a
   * builtin SMT-LIB type, or EUNOIA otherwise.
   * @param typ The given type.
   * @return The meta-kind of typ, or EUNOIA otherwise.
   */
  MetaKind getTypeMetaKind(const Expr& typ) const;
  /**
   * Get the meta kind of the type of expression e.
   * In other words, we return the datatype that e is a constructor of in the
   * final embedding, SMT_BUILTIN if e is a builtin SMT-LIB application, or
   * EUNOIA otherwise.
   * @param s Unused, retained so callers read as state-directed.
   * @param e The given expression.
   * @param cname Updated to the root name of the constructor.
   * @return The meta-kind of the type of e, or EUNOIA otherwise.
   */
  MetaKind getMetaKind(State& s, const Expr& e, std::string& cname) const;

 private:
  /** Whether to emit the signature-specific Logos parser configuration. */
  bool d_generateParser;
  /** Return true if sname denotes a Lean meta symbol supplied by templates. */
  bool isBuiltinMetaSymbol(const std::string& sname) const override;
  /** Print an atomic EO expression in the Lean embedding. */
  void printEmbAtomicTerm(const Expr& c, std::ostream& os);
  /** Print an EO expression as a Lean embedded term. */
  void printEmbTerm(const Expr& c,
                    std::ostream& os,
                    MetaKind tinit = MetaKind::NONE,
                    bool maybeLetify = true);
  /** Recursive implementation of printEmbTerm with let-binding state. */
  void printEmbTermInternal(const Expr& c,
                            std::ostream& os,
                            MetaKind tinit,
                            std::map<const ExprValue*, size_t>& lbind);
  /** Emit all remembered program definitions. */
  void finalizePrograms();
  /**
   * Write program definition to d_defs. For consistency this is also called
   * for define commands.
   * @param v The program variable.
   * @param prog The program definition.
   * @param isDefine True iff this program definition originated from a
   * define command.
   */
  void finalizeProgram(const Expr& v, const Expr& prog, bool isDefine = false);
  /** Emit a declaration into the appropriate Lean embedded datatype. */
  void finalizeDecl(const Expr& e) override;
  /** Return whether t is a program type or program constant. */
  static bool isProgram(const Expr& t);
  /** Emit the Lean checker definitions. */
  void finalizeChecker();
  /** Emit the generated, signature-specific Logos parser configuration. */
  void finalizeParser();
  /**
   * Emit the parser tables for the definitions of the input, see d_parseDefs.
   *
   * @param opNames The names already declared as operators, either by the
   * signature or by the parser template.
   * @param ops The stream of the operators of the signature, to which each
   * definition that takes no arguments is appended as a nullary operator, and
   * each definition that takes arguments as an operator indexed by them.
   * @param macros The stream for the identifiers introduced by a definition
   * that takes arguments, which are bound to a macro that expands to an
   * application of the corresponding operator in ops.
   */
  void finalizeParseDefs(const std::set<std::string>& opNames,
                         std::ostream& ops,
                         std::ostream& macros);
  /** Emit Lean definitions for the SMT model layer. */
  void finalizeSmtModel();
  /** Emit Lean specifications for generated proof-rule targets. */
  void finalizeSpec();
  /** Emit Lean lemma scaffolding for generated specifications. */
  void finalizeLemmas();
  /**
   * Return the Lean symbol name for an embedded SMT operator.
   */
  static std::string getEmbedName(const Expr& oApp,
                                  MetaKind ctx = MetaKind::EUNOIA);
  /** Print one checker step include case. */
  void printStepCase(std::ostream& out, const std::string& str, bool isPop);
  /** Print the empty checker step include case. */
  void printStepEmptyCase(std::ostream& out,
                          const std::string& str,
                          bool isPop);
  /** Return true if c can be printed as an atomic Eunoia term. */
  bool isAtomicEo(const Expr& c, const std::string& cname, size_t& uarity);
  /** Return true if c can be printed as an atomic SMT term. */
  bool isAtomicSmt(const Expr& c, const std::string& cname);
  /**
   * Read the termination clauses of a file into d_terminatingBy. Lean cannot
   * see for itself why some generated definitions terminate, and no measure
   * this plugin could derive would do, so the clause is stated as the Lean
   * text it is and appended to the definition of the program named.
   *
   * A block runs from a line naming one or more programs, written
   * `-- $name ...`, to the next such line; what lies between is the clause.
   * See plugins/lean_meta/termination.lean.
   */
  void readTerminationClauses(const std::string& path);
  /** Generated Lean definitions for programs. */
  std::stringstream d_defs;
  /** Generated mutually recursive total Lean definitions. */
  std::stringstream d_defsTotal;
  /** Whether any generated definitions have been seen. */
  bool d_hasDefs;
  /** Generated helper definitions for Eunoia-object membership. */
  std::stringstream d_eoIsObjDefs;
  /** As above, for programs with simple (non-recursive) definitions. */
  std::stringstream d_eoIsObjDefsSimple;
  /** Eunoia term embedding */
  std::stringstream d_embedTermDt;
  /** Eunoia operator embedding */
  std::stringstream d_embedTOpDt[4];
  /** Eunoia is refutation prop */
  std::stringstream d_eoIsRef;
  /** Generated Lean checker body. */
  std::stringstream d_eoChecker;
  /** SMT definitions */
  std::stringstream d_smtDefs;
  /** Generated Lean SMT helper definitions. */
  std::stringstream d_smt;
  /** SMT term datatype cases. */
  std::stringstream d_smtDt;
  /** SMT theory-operator datatype cases. */
  std::stringstream d_smtTOpDt;
  /** SMT type datatype cases. */
  std::stringstream d_smtTypeDt;
  /** SMT value datatype cases. */
  std::stringstream d_smtValueDt;
  /** SMT type ordering-key cases, see printOrderKeyCase. */
  std::stringstream d_smtTypeKey;
  /** SMT value ordering-key cases, see printOrderKeyCase. */
  std::stringstream d_smtValueKey;
  /** Number of constructors emitted for the SMT type datatype. */
  size_t d_smtTypeNcons = 0;
  /** Number of constructors emitted for the SMT value datatype. */
  size_t d_smtValueNcons = 0;
  /** Checker command datatype cases. */
  std::stringstream d_cmdDt;
  /** Checker rule datatype cases. */
  std::stringstream d_ruleDt;
  /** Rule include cases. */
  std::stringstream d_rlInclude;
  /** Checker step include cases. */
  std::stringstream d_rlIncludeStep;
  /** Checker step-pop include cases. */
  std::stringstream d_rlIncludeStepPop;
  /** List of program definitions */
  std::vector<Expr> d_progDefs;
  /** Map from each program symbol to its definition. */
  std::map<Expr, Expr> d_progToDef;
  /** Programs that originated from define commands. */
  std::set<Expr> d_progIsDefine;
  /** Programs inferred to require total definitions. */
  std::set<Expr> d_totalDefProgs;
  /** Programs inferred to require partial (stuck-extended) definitions. */
  std::set<Expr> d_partialDefProgs;
  /** Programs with simple definitions, i.e. trivially not recursive. */
  std::set<Expr> d_simpleDefProgs;
  /** Return a Lean-safe version of an SMT-LIB identifier. */
  static std::string cleanSmtId(const std::string& id);
  /** Return a Lean-safe version of a general generated identifier. */
  static std::string cleanId(const std::string& id);
  /** Quote a string as a Lean string literal. */
  static std::string quoteLeanString(const std::string& value);

  /** Surface syntax for an operator, preserved by the desugar stage. */
  struct ParserOp
  {
    /** The name of the operator in the surface (user) syntax. */
    std::string d_surface;
    /** The name of the operator in the generated signature. */
    std::string d_generated;
    /** Its number of indices (opaque arguments). */
    size_t d_indexArity;
    /** Its number of ordinary term arguments. */
    size_t d_termArity;
    /** Its syntactic attribute, e.g. "right-assoc-nil", or "none" if none. */
    std::string d_attr;
    /**
     * The constructor operand of `d_attr`: the operator that chains a chainable
     * one, or the one that builds the list of an `arg-list`. "-" if the
     * attribute takes no operand.
     */
    std::string d_connector;
  };
  /** Parser operator records received through desugaring echo metadata. */
  std::vector<ParserOp> d_parserOps;
  /** Surface/generated proof-rule names received through echo metadata. */
  std::vector<std::pair<std::string, std::string>> d_parserRules;
  /**
   * The definitions preserved by the desugar stage, as pairs of the name in
   * the input and the definition, which is a Kind::LAMBDA if the definition
   * takes arguments and its body otherwise. See getParseDefPrefix.
   */
  std::vector<std::pair<std::string, Expr>> d_parseDefs;
  /** Return true if the Lean backend emitted the operator of the record op. */
  bool isEmittedParserOp(const ParserOp& op) const;
  /**
   * Emit the operator declaration for the record op under the given name, which
   * is op.d_surface unless the operator is being declared under an alias
   * introduced by a definition, see finalizeParseDefs.
   */
  void printParserOp(const ParserOp& op,
                     const std::string& name,
                     std::ostream& ops);
  /**
   * Return the Lean term for the nullary operator whose name in the surface
   * syntax is surface, e.g. the operator that chains a chainable one or that
   * builds a gathered list. Empty if the Lean backend did not emit it.
   */
  std::string getParserOpTerm(const std::string& surface) const;
  /**
   * Return a record in d_parserOps for the operator whose name in the generated
   * signature is generated and that the Lean backend emitted, or null if there
   * is none.
   */
  const ParserOp* getParserOpForGenerated(const std::string& generated) const;
  /** UserOp constructors actually emitted by the Lean backend. */
  std::set<std::pair<std::string, size_t>> d_emittedUserOps;
  /** CRule constructors actually emitted by the Lean backend. */
  std::set<std::string> d_emittedRules;
  // TEMPORARY
  /** Programs excluded from partial-definition generation, by name. */
  std::unordered_set<std::string> d_partialExc;
  /**
   * Maps program names to the termination annotation and proof that is
   * appended to their generated definition, as read by
   * readTerminationClauses.
   */
  std::map<std::string, std::string> d_terminatingBy;
};

}  // namespace ethos

#endif
