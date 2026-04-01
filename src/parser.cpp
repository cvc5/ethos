/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#include "parser.h"

namespace ethos {

Parser::Parser(State& s, bool isSignature, bool isReference)
    // only (optionally) lex let when reference parsing, only lex Type if
    // signature.
    : d_lex(!isSignature && s.getOptions().d_parseLet, isSignature),
      d_state(s),
      d_eparser(d_lex, d_state, isSignature),
      d_cmdParser(d_lex, d_state, d_eparser, isReference)
{
}

void Parser::setFileInput(const std::string& filename)
{
  d_input = Input::mkFileInput(filename);
  d_lex.initialize(d_input.get(), filename);
}

void Parser::setStreamInput(std::istream& input)
{
  d_input = Input::mkStreamInput(input);
  d_lex.initialize(d_input.get(), "stream");
}

void Parser::setStringInput(const std::string& input)
{
  d_input = Input::mkStringInput(input);
  d_lex.initialize(d_input.get(), "string");
}

bool Parser::parseNextCommand()
{
  return d_cmdParser.parseNextCommand();
}

Expr Parser::parseNextExpr()
{
  return d_eparser.parseExpr();
}

}  // namespace ethos
