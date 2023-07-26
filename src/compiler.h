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
  /** Identifier counts */
  size_t d_idCount;
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
  /** Maps expressions to identifiers */
  std::map<ExprValue*, size_t> d_idMap;
  /** Write expression, return identifier */
  size_t writeExpr(std::ostream& os, const Expr& e);
};

}  // namespace alfc

#endif /* STATE_H */
