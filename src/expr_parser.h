#ifndef EXPR_PARSER_H
#define EXPR_PARSER_H

#include "expr.h"
#include "state.h"
#include "lexer.h"
#include "attr.h"

namespace alfc {

/**
 * The smt2 term parser, which parses terms, sorts, symbol expressions
 * and other miscellaneous expressions from the SMT2 language. It reads
 * from the given lexer.
 */
class ExprParser
{
 public:
  ExprParser(Lexer& lex, State& state);
  virtual ~ExprParser() {}

  /** Parses an SMT-LIB term <term> */
  Expr parseExpr();
  /** Parses an SMT-LIB type <type> */
  Expr parseType();
  /** Parses parentheses-enclosed term list (<term>*) */
  std::vector<Expr> parseExprList();
  /** Parses parentheses-enclosed term list ((<term> <term>)*) */
  std::vector<Expr> parseExprPairList();
  /**
   * Parse parentheses-enclosed sorted variable list of the form:
   * ((<symbol> <sort>)*)
   */
  std::vector<Expr> parseAndBindSortedVarList();
  /**
   * Parse symbol, which returns the string of the parsed symbol if the next
   * token is a valid smt2 symbol.
   *
   * @param check Specifies whether to check if the symbol is already declared
   * or not declared,
   * @param type The type of symbol we are expecting (variable or sort).
   */
  std::string parseSymbol();
  /**
   * Parse parentheses-enclosed symbol list.
   * Expects to parse '(<symbol>*)', where '<symbol>' is parsed by the above
   * method.
   */
  std::vector<std::string> parseSymbolList();
  /**
   * Parse datatype def '<datatype_dec>', not parentheses enclosed. The syntax
   * for datatype declarations is:
   *
   * datatype_dec :=
   *   (<constructor_dec>+) | (par (<symbol>+) (<constructor_dec>+))
   * constructor_dec := (<symbol> (<symbol> <sort>)∗)
   */
  bool parseDatatypesDef(
      const std::vector<std::string>& dnames,
      const std::vector<size_t>& arities,
      std::map<Expr, std::vector<Expr>>& dts,
      std::map<Expr, std::vector<Expr>>& dtcons);
  /**
   * Parses ':X', returns 'X'
   */
  std::string parseKeyword();
  /** Parse integer numeral */
  uint32_t parseIntegerNumeral();
  /**
   * Matches a string, and (optionally) strips off the quotes/unescapes the
   * string when `unescape` is set to true.
   */
  std::string parseStr(bool unescape);
  
  /**
   * Parse attribute list
   * <attr_1> ... <attr_n>
   * 
   * @param e The expression we are applying to
   */
  void parseAttributeList(const Expr& e, std::map<Attr, Expr>& attrs);
  
  /**
   * Parse literal kind.
   */
  Kind parseLiteralKind();
  //-------------------------- checking
  /** type check the expression */
  Expr typeCheck(Expr& e);
  /** ensure type */
  Expr typeCheck(Expr& e, const Expr& expected);
  /** get variable, else error */
  Expr getVar(const std::string& name);
  /** Bind, or throw error otherwise */
  void bind(const std::string& name, Expr& e);
  /** Ensure bound */
  void ensureBound(Expr& e, const std::vector<Expr>& bvs);
  //-------------------------- end checking
 protected:
  /**
   * Parse constructor definition list, add to declaration type. The expected
   * syntax is '(<constructor_dec>+)'.
   */
  bool parseConstructorDefinitionList(Expr& dt,
                                      std::vector<Expr>& conslist,
                                      std::map<Expr, std::vector<Expr>>& dtcons);
  /** Return the unsigned for the current token string. */
  uint32_t tokenStrToUnsigned();
  /**
   * Return the string content of the current token string when interpreted
   * as the given token, e.g. return`abc` for token string `|abc|` where
   * tok is QUOTED_SYMBOL.
   */
  std::string tokenStrToSymbol(Token tok);
  /**
   * Unescape string, which updates s based on processing escape sequences
   * as defined in SMT2.
   */
  void unescapeString(std::string& s);
  /** The lexer */
  Lexer& d_lex;
  /** The state */
  State& d_state;
  /** Strings to attributes */
  std::map<std::string, Attr> d_strToAttr;
  /** Mapping symbols to literal kinds */
  std::map<std::string, Kind> d_strToLiteralKind;
};

}  // namespace cvc5

#endif /* TERM_PARSER_H */
