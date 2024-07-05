/******************************************************************************
 * This file is part of the alfc project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
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
  CmdParser(Lexer& lex,
            State& state,
            ExprParser& eparser,
            bool isReference);
  virtual ~CmdParser() {}
  /**
   * Parse the next command, return false if we are at the end of file.
   */
  bool parseNextCommand();
 protected:
  /** Next command token */
  Token nextCommandToken();
  /** The lexer */
  Lexer& d_lex;
  /** The state */
  State& d_state;
  /** Reference to the stats */
  Stats& d_sts;
  /** The term parser */
  ExprParser& d_eparser;
  /** Map strings to tokens */
  std::map<std::string, Token> d_table;
  /** */
  bool d_isReference;
  /** Is finished */
  bool d_isFinished;
  /** Stats enabled? */
  bool d_statsEnabled;
};

}  // namespace alfc

#endif /* H */
