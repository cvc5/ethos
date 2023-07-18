/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The smt2 command parser.
 */

#include "cmd_parser.h"

namespace atc {

CmdParser::CmdParser(Lexer& lex,
                             State& state,
                             ExprParser& eparser)
    : d_lex(lex), d_state(state), d_eparser(eparser)
{
  // initialize the command tokens
  d_table["assume"] = Token::ASSUME_TOK;
  d_table["declare-const"] = Token::DECLARE_CONST_TOK;
  d_table["declare-fun"] = Token::DECLARE_FUN_TOK;
  d_table["declare-sort"] = Token::DECLARE_SORT_TOK;
  d_table["define-const"] = Token::DEFINE_CONST_TOK;
  d_table["define-fun"] = Token::DEFINE_FUN_TOK;
  d_table["define-sort"] = Token::DEFINE_SORT_TOK;
  d_table["echo"] = Token::ECHO_TOK;
  d_table["exit"] = Token::EXIT_TOK;
  d_table["include"] = Token::INCLUDE_TOK;
  d_table["reset"] = Token::RESET_TOK;
  d_table["set-info"] = Token::SET_INFO_TOK;
  d_table["set-option"] = Token::SET_OPTION_TOK;
}

Token CmdParser::nextCommandToken()
{
  Token tok = d_lex.nextToken();
  // symbols as commands
  if (tok == Token::SYMBOL)
  {
    std::string str(d_lex.tokenStr());
    std::map<std::string, Token>::iterator it = d_table.find(str);
    if (it != d_table.end())
    {
      return it->second;
    }
  }
  return tok;
}

bool CmdParser::parseNextCommand()
{
  // if we are at the end of file, return the null command
  if (d_lex.eatTokenChoice(Token::EOF_TOK, Token::LPAREN_TOK))
  {
    return false;
  }
  Token tok = nextCommandToken();
  switch (tok)
  {
    // (declare-fun <symbol> (<sort>∗) <sort>)
    // (declare-const <symbol> <sort>)
    case Token::DECLARE_CONST_TOK:
    case Token::DECLARE_FUN_TOK:
    {
      //d_state.checkThatLogicIsSet();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      std::vector<Expr> sorts;
      if (tok == Token::DECLARE_FUN_TOK)
      {
        sorts = d_eparser.parseExprList();
      }
      Expr t = d_eparser.parseExpr();
      if (!sorts.empty())
      {
        t = d_state.mkFunctionType(sorts, t);
      }
      Expr v = d_state.mkVar(name, t);
      d_state.bind(name, v);
    }
    break;
    // (declare-sort <symbol> <numeral>)
    case Token::DECLARE_SORT_TOK:
    {
      //d_state.checkThatLogicIsSet();
      //d_state.checkLogicAllowsFreeExprs();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      size_t arity = d_eparser.parseIntegerNumeral();
      Expr type;
      Expr ttype = d_state.mkType();
      if (arity == 0)
      {
        type = ttype;
      }
      else
      {
        std::vector<Expr> args;
        for (size_t i=0; i<arity; i++)
        {
          args.push_back(ttype);
        }
        type = d_state.mkFunctionType(args, ttype);
      }
      Expr decType = d_state.mkVar(name, ttype);
      d_state.bind(name, decType);
    }
    break;
    // TODO (declare-type <symbol> ...)
    // (define-const <symbol> <sort> <term>)
    case Token::DEFINE_CONST_TOK:
    {
      //d_state.checkThatLogicIsSet();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      Expr t = d_eparser.parseExpr();
      Expr e = d_eparser.parseExpr();
      // TODO: type check?
      d_state.bind(name, e);
    }
    break;
    // (define-fun <symbol> (<sorted_var>*) <sort> <term>)
    case Token::DEFINE_FUN_TOK:
    {
      //d_state.checkThatLogicIsSet();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      std::vector<std::pair<std::string, Expr>> sortedVarNames =
          d_eparser.parseSortedVarList();
      Expr ret = d_eparser.parseExpr();
      if (sortedVarNames.size() > 0)
      {
        d_state.pushScope();
      }
      std::vector<Expr> vars = d_state.mkAndBindVars(sortedVarNames);
      Expr expr = d_eparser.parseExpr();
      if (sortedVarNames.size() > 0)
      {
        d_state.popScope();
        Expr vl = d_state.mkExpr(Kind::VARIABLE_LIST, vars);
        expr = d_state.mkExpr(Kind::LAMBDA, {vl, expr});
      }
      d_state.bind(name, expr);
    }
    break;
    // (define-sort <symbol> (<symbol>*) <sort>)
    case Token::DEFINE_SORT_TOK:
    {
      //d_state.checkThatLogicIsSet();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      std::vector<std::string> snames =
          d_eparser.parseSymbolList();
      d_state.pushScope();
      std::vector<Expr> sorts;
      Expr ttype = d_state.mkType();
      for (const std::string& sname : snames)
      {
        sorts.push_back(d_state.mkVar(sname, ttype));
      }
      Expr t = d_eparser.parseExpr();
      d_state.popScope();
    }
    break;
    // (echo <string>)
    case Token::ECHO_TOK:
    {
      // optional string literal
      tok = d_lex.peekToken();
      if (tok == Token::STRING_LITERAL)
      {
        std::string msg = d_eparser.parseStr(true);
        //cmd.reset(new EchoCommand(msg));
      }
      else
      {
        //cmd.reset(new EchoCommand());
      }
    }
    break;
    // (exit)
    case Token::EXIT_TOK:
    {
      exit(0);
    }
    break;
    // (reset)
    case Token::RESET_TOK:
    {
      //cmd.reset(new ResetCommand());
      // reset the state of the parser, which is independent of the symbol
      // manager
      d_state.reset();
    }
    break;
    // (set-info <attribute>)
    case Token::SET_INFO_TOK:
    {
      std::string key = d_eparser.parseKeyword();
      //Expr sexpr = d_eparser.parseSymbolicExpr();
      //cmd.reset(new SetInfoCommand(key, sexprToString(sexpr)));
    }
    break;
    // (set-logic <symbol>)
    case Token::SET_LOGIC_TOK:
    {
      std::string name = d_eparser.parseSymbol();
      // replace the logic with the forced logic, if applicable.
      //d_state.setLogic(lname);
      //cmd.reset(new SetBenchmarkLogicCommand(lname));
    }
    break;
    // (set-option <option>)
    case Token::SET_OPTION_TOK:
    {
      std::string key = d_eparser.parseKeyword();
      //Expr sexpr = d_eparser.parseSymbolicExpr();
      //std::string ss = sexprToString(sexpr);
      //cmd.reset(new SetOptionCommand(key, ss));
    }
    break;
    case Token::EOF_TOK:
      d_lex.parseError("Expected SMT-LIBv2 command", true);
      break;
    default:
      d_lex.unexpectedTokenError(tok, "Expected SMT-LIBv2 command");
      break;
  }
  d_lex.eatToken(Token::RPAREN_TOK);
  return true;
}

}  // namespace atc
