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

/**
 * A scope of declared variables.
 * 
 * This class maintains two streams, a declaration stream where the expressions
 * are declared, and an output stream where they are constructed.
 */
class CompilerScope
{
public:
  /**
   * @param decl The declaration stream
   * @param out The output stream
   * @param prefix The prefix for naming variables
   * @param global The global scope. If this is non-null, then ground terms
   * are instead declared/constructed on the given global scope. If this is
   * null, then this is the global scope.
   * @param progEval Whether programs should be evaluated. If true, then
   * the output stream will call evaluation, if false then it will construct
   * applications of programs.
   */
  CompilerScope(std::ostream& decl,
                std::ostream& out,
                const std::string& prefix,
                CompilerScope* global = nullptr,
                bool progEval = false);
  ~CompilerScope();
  /** Ensure that ev has been declared, return its identifier */
  size_t ensureDeclared(const Expr& ev);
  /** Ensure that each expression in ev is declared */
  void ensureDeclared(const std::vector<Expr>& ev);
  /** is global */
  bool isGlobal() const;
  /** get name for */
  std::string getNameFor(const Expr& e) const;
  /** allocate subscope */
  size_t allocateSubscope();

  /** Reference to the declare stream */
  std::ostream& d_decl;
  /** Reference to the output stream */
  std::ostream& d_out;
  /** Prefix */
  std::string d_prefix;
  /** Whether program applications constructed in this scope are evaluated */
  bool d_progEval;
  /** Maps expressions to identifiers */
  std::map<const ExprValue*, size_t> d_idMap;

 private:
  /** Identifier counts */
  size_t d_idCount;
  /** Subscope count */
  size_t d_subscopeCount;
  /** Pointer to global context, null if this is the global context */
  CompilerScope* d_global;
};

/**
 * Maintains path accesses to an expression given by name prefix.
 * In particular, this will write accesses e.g. for prefix "a":
 *   Expr& a2 = a->getChildren()[2];
 *   Expr& a3 = a->getChildren()[3];
 *   Expr& a31 = a3->getChildren()[1];
 *   Expr& a30 = a3->getChildren()[0];
 *   Expr& a301 = a30->getChildren()[1];
 *   Expr& a300 = a30->getChildren()[0];
 * to the given declaration stream.
 */
class PathTrie
{
public:
  /**
   * @param decl The declaration stream
   * @param prefix The prefix for naming variables
   */
  PathTrie(std::ostream& decl, const std::string& prefix);
  std::string getNameForPath(const std::vector<size_t>& path);
  /** The stream for declarations */
  std::ostream& d_decl;
  /** mark that the given path should be declared */
  void markDeclared(const std::vector<size_t>& path);
private:
  /** The prefix */
  std::string d_prefix;
  class PathTrieNode
  {
  public:
    PathTrieNode() : d_decl(false) {}
    /** Children */
    std::map<size_t, PathTrieNode> d_children;
    /** Whether the reference for this path has been declared yet */
    bool d_decl;
    /**
     * Get name for path, returns the name on the path, e.g. a301 where
     * prefix="a", path={3,0,1}.
     */
    std::string getNameForPath(std::ostream& osdecl,
                               const std::string& prefix,
                               const std::vector<size_t>& path);
  };
  /** Trie for managing declarations */
  PathTrieNode d_trie;
};

/**
 * The compiler class, which listens to the calls to State and generates
 * C++ code for replaying those calls during initialization and for
 * compiled type checking, term substitution, and side condition matching.
 */
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
  /** Set type rule for literal kind k to t */
  void setLiteralTypeRule(Kind k, const Expr& t);
  /** */
  void bind(const std::string& name, const Expr& e);
  /** Mark attributes */
  void markConstructorKind(const Expr& v, Attr a, const Expr& cons);
  /** Mark oracle command */
  void markOracleCmd(const Expr& v, const std::string& ocmd);
  /** Define program */
  void defineProgram(const Expr& v, const Expr& prog);
  /** Define constructor */
  void defineConstructor(const Expr& c, const std::vector<Expr>& sels);
  /** Define datatype */
  void defineDatatype(const Expr& d, const std::vector<Expr>& cons);
  /** To string, which returns the compiled C++ code for the given run */
  std::string toString();
private:
  State& d_state;
  TypeChecker& d_tchecker;
  /** Number of current scopes. Bindings at scope>0 are not remembered */
  size_t d_nscopes;
  /** Declarations? */
  std::stringstream d_decl;
  /** code to be performed on --show-config */
  std::stringstream d_config;
  std::stringstream d_configEnd;
  /** code to be performed on initialization */
  std::stringstream d_init;
  std::stringstream d_initEnd;
  /**
   * Code to be called for type checking applications terms
   */
  std::stringstream d_tc;
  std::stringstream d_tcEnd;
  /**
   * Code to be called for evaluating terms (substitutions)
   */
  std::stringstream d_eval;
  std::stringstream d_evalEnd;
  /**
   * Code to be called for evaluating programs (matching), returns the case
   */
  std::stringstream d_evalp;
  std::stringstream d_evalpEnd;
  /** Identifier counts */
  CompilerScope d_global;
  /**
   * Run identifiers, allocated for terms that we have compiled type checking or evaluation for.
   * Uses the same identifiers as in d_idMap.
   */
  std::map<const ExprValue*, size_t> d_runIdMap;
  /** */
  std::unordered_set<const ExprValue*> d_tcWritten;
  std::unordered_set<const ExprValue*> d_evalWritten;
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
   * Write type checking code for e.
   */
  void writeTypeChecking(std::ostream& os, const Expr& e);
  /**
   * Write evaluation code for e.
   */
  void writeEvaluate(std::ostream& os, const Expr& e);
  /**
   * Write matching code for matching an expression to pat.
   * 
   * @param pat The pattern to match
   * @param initPath The initial path of the variable we are matching.
   * @param pt The datastructure that maintains accesses to the expression
   * we are matching to pat
   * 
   */
  void writeMatching(const Expr& pat,
                     std::vector<size_t>& initPath,
                     PathTrie& pt,
                     std::vector<std::string>& reqs,
                     std::map<const ExprValue*, std::string>& varAssign,
                     const std::string& failCmd);
  /** 
   * Write requirements, which writes an if statement whose conditions are
   * reqs, and whose body is failCmd.
   */
  void writeRequirements(std::ostream& os, 
                         const std::vector<std::string>& reqs, 
                         const std::string& failCmd);
  /** write argument list */
  void writeArgumentList(std::ostream& os,
                         const std::vector<Expr>& args);
};

}  // namespace alfc

#endif /* STATE_H */
