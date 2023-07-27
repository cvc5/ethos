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

class CompilerScope
{
public:
  CompilerScope(std::ostream& decl, std::ostream& out, const std::string& prefix, bool isGlobal = false);
  ~CompilerScope();
  /** allocate id */
  size_t ensureDeclared(ExprValue* ev);
  /** is global */
  bool isGlobal() const;

  /** Reference to the declare stream */
  std::ostream& d_decl;
  /** Reference to the declare stream */
  std::ostream& d_out;
  /** Prefix */
  std::string d_prefix;
  /** Identifier counts */
  size_t d_idCount;
  /** Maps expressions to identifiers */
  std::map<ExprValue*, size_t> d_idMap;
  /** Is global */
  bool d_isGlobal;
  /** Get name for path */
  std::string getNameForPath(const std::string& t, const std::vector<size_t>& path);
 private:
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
  size_t writeExprInternal(const Expr& e, CompilerScope& cs);
  /**
   * Write type checking code for t
   */
  void writeTypeChecking(std::ostream& os, const Expr& e);
  /**
   * Write evaluation
   */
  size_t writeEvaluation(std::ostream& os, const Expr& e);
  /** Write matching code for */
  void writeMatching(std::vector<Expr>& pats,
                      const std::string& t,
                      CompilerScope& s,
                      std::vector<std::string>& reqs,
                      std::map<Expr, std::string>& varAssign);
};

}  // namespace alfc

#endif /* STATE_H */
