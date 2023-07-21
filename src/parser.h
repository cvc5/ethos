#ifndef PARSER_H
#define PARSER_H

#include "state.h"
#include "cmd_parser.h"
#include "lexer.h"
#include "expr_parser.h"
#include "input.h"

namespace alfc {

/**
 * Flex-based smt2 parser. It maintains a lexer, a state, a term parser and a
 * command parser. The latter two are used for parsing terms and commands. The
 * command parser depends on the term parser.
 */
class Parser
{
 public:
  Parser(State& s);
  virtual ~Parser() {}
  
  /** Set the input for the given file.
   *
   * @param filename the input filename
   */
  void setFileInput(const std::string& filename);
  /**
   * Parse and return the next command. Will initialize the logic to "ALL"
   * or the forced logic if no logic is set prior to this point and a command
   * is read that requires initializing the logic.
   */
  bool parseNextCommand();

 protected:
  /** The input */
  std::unique_ptr<Input> d_input;
  /** The lexer */
  Lexer d_lex;
  /** The state */
  State& d_state;
  /** Expression parser */
  ExprParser d_eparser;
  /** Command parser */
  CmdParser d_cmdParser;
};

}  // namespace alfc

#endif /* PARSER_H */
