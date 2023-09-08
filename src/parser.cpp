#include "parser.h"

namespace alfc {

Parser::Parser(State& s, bool isReference)
    : d_lex(),
      d_state(s),
      d_eparser(d_lex, d_state),
      d_cmdParser(d_lex, d_state, d_eparser, isReference)
{
}

void Parser::setFileInput(const std::string& filename)
{
  d_input = Input::mkFileInput(filename);
  d_lex.initialize(d_input.get(), filename);
}

void Parser::setStringInput(const std::string& input)
{
  d_input = Input::mkStringInput(input);
  d_lex.initialize(d_input.get(), input);
}
  
bool Parser::parseNextCommand()
{
  return d_cmdParser.parseNextCommand();
}

Expr Parser::parseNextExpr()
{
  return d_eparser.parseExpr();
}

}  // namespace alfc
