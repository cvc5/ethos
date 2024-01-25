/******************************************************************************
 * This file is part of the alfc project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef PARSER_H
#define PARSER_H

#include "state.h"
#include "cmd_parser.h"
#include "lexer.h"
#include "expr_parser.h"
#include "input.h"

namespace alfc {

/**
 * smt2 parser. It maintains a lexer, a state, a term parser and a
 * command parser. The latter two are used for parsing terms and commands. The
 * command parser depends on the term parser.
 */
class Parser
{
 public:
  /**
   * @param s The state to populate
   * @param isReference Whether we are parsing a reference file
   */
  Parser(State& s, bool isReference = false);
  virtual ~Parser() {}
  
  /** Set the input for the given file.
   *
   * @param filename the input filename
   */
  void setFileInput(const std::string& filename);
  /** Set the input for the given stream.
   *
   * @param input the input stream
   */
  void setStreamInput(std::istream& input);
  /** Set the string input for the given file.
   *
   * @param filename the input
   */
  void setStringInput(const std::string& input);
  /**
   * Parse and return the next command. Will initialize the logic to "ALL"
   * or the forced logic if no logic is set prior to this point and a command
   * is read that requires initializing the logic.
   */
  bool parseNextCommand();
  /**
   * Parse and return the next term.
   */
  Expr parseNextExpr();

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
