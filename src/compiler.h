#ifndef COMPILER_H
#define COMPILER_H

#include <map>
#include <set>
#include <string>
#include <sstream>
#include <filesystem>

#include "attr.h"
#include "expr.h"
#include "expr_info.h"
#include "expr_trie.h"
#include "type_checker.h"

namespace alfc {

class State;
class TypeChecker;

class CompilerScope
{
public:
  CompilerScope(std::ostream& decl,
                std::ostream& out,
                const std::string& prefix,
                CompilerScope* global = nullptr,
                bool progEval = false);
  ~CompilerScope();
  /** allocate id */
  size_t ensureDeclared(ExprValue* ev);
  void ensureDeclared(std::vector<Expr>& ev);
  /** is global */
  bool isGlobal() const;
  /** get name for */
  std::string getNameFor(Expr& e) const;

  /** Reference to the declare stream */
  std::ostream& d_decl;
  /** Reference to the declare stream */
  std::ostream& d_out;
  /** Prefix */
  std::string d_prefix;
  /** Identifier counts */
  size_t d_idCount;
  /** Whether program applications constructed in this scope are evaluated */
  bool d_progEval;
  /** Maps expressions to identifiers */
  std::map<ExprValue*, size_t> d_idMap;
  /** Get name for path */
  std::string getNameForPath(const std::string& t, const std::vector<size_t>& path);
 private:
  /** Pointer to global context, null if this is the global context */
  CompilerScope* d_global;
  class PathTrie
  {
  public:
    PathTrie() : d_decl(false) {}
    std::map<size_t, PathTrie> d_children;
    bool d_decl;
  };
  std::map<std::string, PathTrie> d_pathMap;
};

class Compiler
{
  friend class TypeChecker;
public:
  Compiler(State& s);
  ~Compiler();
  /** Reset */
  void reset();
  /** Push scope */
  void pushScope();
  /** Pop scope */
  void popScope();
  /** include file, if not already done */
  void includeFile(const std::string& s);
  /** add assumption */
  void addAssumption(const Expr& a);
  /** */
  void bind(const std::string& name, const Expr& e);
  /**
   * Mark attributes
   *
   * Assumes that v is already allocated
   */
  void markAttributes(const Expr& v, const std::map<Attr, Expr>& attrs);
  /** Define program */
  void defineProgram(const Expr& v, const Expr& prog);
  /** Write */
  std::string toString();
private:
  State& d_state;
  TypeChecker& d_tchecker;
  /** Number of current scopes. Bindings at scope>0 are not remembered */
  size_t d_nscopes;
  /** Declarations? */
  std::stringstream d_decl;
  /** code to be performed on initialization */
  std::stringstream d_init;
  std::stringstream d_initEnd;
  /**
   * Code to be called for type checking applications terms
   */
  std::stringstream d_tc;
  std::stringstream d_tcEnd;
  /**
   * Code to be called for evaluating terms
   */
  std::stringstream d_eval;
  std::stringstream d_evalEnd;
  /**
   * Code to be called for evaluating programs, returns the case
   */
  std::stringstream d_evalp;
  std::stringstream d_evalpEnd;
  /** Identifier counts */
  CompilerScope d_global;
  /**
   * Run identifiers, allocated for terms that we have compiled type checking or evaluation for.
   * Uses the same identifiers as in d_idMap.
   */
  std::map<ExprValue*, size_t> d_runIdMap;
  /** */
  std::unordered_set<ExprValue*> d_tcWritten;
  std::unordered_set<ExprValue*> d_evalWritten;
  /** Write run id */
  size_t markCompiled(std::ostream& os, const Expr& e);
  /**
   * Write expression, return identifier.
   *
   * Ensures that returned size_t i is such that _e`i` is in scope.
   */
  size_t writeGlobalExpr(const Expr& e);
  /**
   * Ensures that returned size_t i is such that `<prefix>``i` is in scope,
   * where <prefix> is the prefix for names in cs.
   * 
   * It should be the case that either e is non-ground, or cs is the global
   * scope.
   */
  size_t writeExprInternal(const Expr& e, CompilerScope& cs);
  /**
   * Write type checking code for t.
   */
  void writeTypeChecking(std::ostream& os, const Expr& e);
  /**
   * Write evaluation code
   */
  void writeEvaluate(std::ostream& os, const Expr& e);
  /**
   * Write program evaluation
   */
  size_t writeProgramEvaluation(std::ostream& os, const Expr& p, std::vector<Expr>& cases);
  /** Write matching code for */
  void writeMatching(Expr& pat,
                      const std::string& t,
                      CompilerScope& s,
                      std::vector<std::string>& reqs,
                      std::map<Expr, std::string>& varAssign,
                      const std::string& failCmd);
  /** Get the free symbols */
  std::vector<Expr> getFreeSymbols(const Expr& e) const;
  /** Get the free symbols */
  bool hasVariable(const Expr& e, const std::unordered_set<Expr>& terms) const;
};

}  // namespace alfc

#endif /* STATE_H */
