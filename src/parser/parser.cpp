/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#include "parser/parser.h"

#include <sstream>

namespace ethos {

Parser::Parser(State& s, bool isSignature, bool isReference)
    // only (optionally) lex let when reference parsing, only lex Type if
    // signature.
    : d_lex(!isSignature && s.getOptions().d_parseLet, isSignature),
      d_state(s),
      d_eparser(d_lex, d_state, isSignature, isReference),
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

void Parser::parseAllCommands()
{
  while (parseNextCommand())
  {
  }
  if (d_state.getAssumptionLevel() != 0)
  {
    // report via the lexer, so that this is an ordinary error message
    std::stringstream ss;
    ss << "This file did not preserve assumption scope. The most recent open "
          "assumption was "
       << d_state.getOpenAssumptionName() << ".";
    d_lex.parseError(ss.str());
  }
}

Expr Parser::parseNextExpr()
{
  return d_eparser.parseExpr();
}

void ParserFileReader::readFile(State& s,
                                const Filepath& path,
                                bool isSignature,
                                bool isReference)
{
  Parser p(s, isSignature, isReference);
  p.setFileInput(path.getRawPath());
  p.parseAllCommands();
}

}  // namespace ethos
