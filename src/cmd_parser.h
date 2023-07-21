#ifndef CMD_PARSER_H
#define CMD_PARSER_H

#include <map>

#include "state.h"
#include "lexer.h"
#include "expr_parser.h"

namespace alfc {

/**
 * The smt2 command parser, which parses commands. It reads from the given
 * lexer, and relies on a term parser for parsing terms in the body of commands.
 */
class CmdParser
{
 public:
  CmdParser(Lexer& lex, State& state, ExprParser& eparser);
  virtual ~CmdParser() {}
  /**
   * Parse the next command, return false if we are at the end of file.
   */
  bool parseNextCommand();
 protected:
  /** Bind, or throw error otherwise */
  void bind(const std::string& name, const Expr& e);
  /** Next command token */
  Token nextCommandToken();
  /** The lexer */
  Lexer& d_lex;
  /** The state */
  State& d_state;
  /** The term parser */
  ExprParser& d_eparser;
  /** Map strings to tokens */
  std::map<std::string, Token> d_table;
  /** is strict */
  bool d_isStrict;
  /** is sygus */
  bool d_isSygus;
};

}  // namespace alfc

#endif /* H */
