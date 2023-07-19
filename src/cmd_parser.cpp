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

#include <iostream>

namespace atc {

CmdParser::CmdParser(Lexer& lex,
                             State& state,
                             ExprParser& eparser)
    : d_lex(lex), d_state(state), d_eparser(eparser)
{
  // initialize the command tokens
  d_table["assume"] = Token::ASSUME;
  d_table["declare-const"] = Token::DECLARE_CONST;
  d_table["declare-fun"] = Token::DECLARE_FUN;
  d_table["declare-sort"] = Token::DECLARE_SORT;
  d_table["declare-type"] = Token::DECLARE_TYPE;
  d_table["define-const"] = Token::DEFINE_CONST;
  d_table["define-fun"] = Token::DEFINE_FUN;
  d_table["define-type"] = Token::DEFINE_TYPE;
  d_table["define-sort"] = Token::DEFINE_SORT;
  d_table["echo"] = Token::ECHO;
  d_table["exit"] = Token::EXIT;
  d_table["include"] = Token::INCLUDE;
  d_table["proof"] = Token::PROOF;
  d_table["reset"] = Token::RESET;
  d_table["set-info"] = Token::SET_INFO;
  d_table["set-option"] = Token::SET_OPTION;
  d_table["step"] = Token::STEP;
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
  if (d_lex.eatTokenChoice(Token::EOF_TOK, Token::LPAREN))
  {
    return false;
  }
  Token tok = nextCommandToken();
  switch (tok)
  {
    // (assume <symbol> <term>)
    case Token::ASSUME:
    {
      std::string name = d_eparser.parseSymbol();
      // parse what is proven
      Expr proven = d_eparser.parseExpr();
      // FIXME: proofs are simple for now
      Expr pt = d_state.mkProofType();
      Expr v = d_state.mkConst(name, pt);
      d_state.bind(name, v);
    }
    break;
    // (declare-fun <symbol> (<sort>∗) <sort>)
    // (declare-const <symbol> <sort>)
    case Token::DECLARE_CONST:
    case Token::DECLARE_FUN:
    {
      //d_state.checkThatLogicIsSet();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      std::vector<Expr> sorts;
      if (tok == Token::DECLARE_FUN)
      {
        sorts = d_eparser.parseExprList();
      }
      Expr t = d_eparser.parseExpr();
      if (!sorts.empty())
      {
        t = d_state.mkFunctionType(sorts, t);
      }
      Expr v = d_state.mkConst(name, t);
      d_state.bind(name, v);
    }
    break;
    // (declare-sort <symbol> <numeral>)
    case Token::DECLARE_SORT:
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
      Expr decType = d_state.mkConst(name, ttype);
      d_state.bind(name, decType);
    }
    break;
    // (declare-type <symbol> (<sort>*))
    case Token::DECLARE_TYPE:
    {
      //d_state.checkThatLogicIsSet();
      //d_state.checkLogicAllowsFreeExprs();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      std::vector<Expr> args = d_eparser.parseExprList();
      Expr type;
      Expr ttype = d_state.mkType();
      if (args.empty())
      {
        type = ttype;
      }
      else
      {
        // TODO: ensure args are types?
        type = d_state.mkFunctionType(args, ttype);
      }
      Expr decType = d_state.mkConst(name, type);
      d_state.bind(name, decType);
    }
    break;
    // (define-const <symbol> <sort> <term>)
    case Token::DEFINE_CONST:
    {
      //d_state.checkThatLogicIsSet();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      Expr t = d_eparser.parseExpr();
      Expr e = d_eparser.parseExpr();
      // TODO: ensure t has type e?
      d_state.bind(name, e);
    }
    break;
    // (define-fun <symbol> (<sorted_var>*) <sort> <term>)
    case Token::DEFINE_FUN:
    case Token::DEFINE_TYPE:
    {
      //d_state.checkThatLogicIsSet();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      std::vector<std::pair<std::string, Expr>> sortedVarNames =
          d_eparser.parseSortedVarList();
      Expr ret;
      if (tok == Token::DEFINE_FUN)
      {
        ret = d_eparser.parseExpr();
      }
      else
      {
        ret = d_state.mkType();
      }
      if (sortedVarNames.size() > 0)
      {
        d_state.pushScope();
      }
      std::vector<Expr> vars;
      if (!d_state.mkAndBindVars(sortedVarNames, vars))
      {
        // TODO: parse error
      }
      Expr expr = d_eparser.parseExpr();
      if (sortedVarNames.size() > 0)
      {
        d_state.popScope();
        Expr vl = d_state.mkExpr(Kind::VARIABLE_LIST, vars);
        expr = d_state.mkExpr(Kind::LAMBDA, {vl, expr});
      }
      // TODO: ensure the return type is ret?
      d_state.bind(name, expr);
    }
    break;
    // (define-sort <symbol> (<symbol>*) <sort>)
    case Token::DEFINE_SORT:
    {
      //d_state.checkThatLogicIsSet();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      std::vector<std::string> snames =
          d_eparser.parseSymbolList();
      if (!snames.empty())
      {
        d_state.pushScope();
        std::vector<Expr> sorts;
        Expr ttype = d_state.mkType();
        for (const std::string& sname : snames)
        {
          Expr v = d_state.mkVar(sname, ttype);
          d_state.bind(sname, v);
        }
      }
      Expr t = d_eparser.parseExpr();
      if (!snames.empty())
      {
        d_state.popScope();
      }
      d_state.bind(name, t);
    }
    break;
    // (echo <string>)
    case Token::ECHO:
    {
      // optional string literal
      tok = d_lex.peekToken();
      if (tok == Token::STRING_LITERAL)
      {
        std::string msg = d_eparser.parseStr(true);
        std::cout << msg << std::endl;
      }
      else
      {
        std::cout << std::endl;
      }
    }
    break;
    // (exit)
    case Token::EXIT:
    {
      exit(0);
    }
    break;
    case Token::INCLUDE:
    {
      tok = d_lex.peekToken();
      if (tok == Token::STRING_LITERAL)
      {
        d_lex.parseError("Expected string literal for include");
      }
      
    }
    break;
    // (proof t)
    case Token::PROOF:
    {
      Expr proven = d_eparser.parseExpr();
      // TODO: ensure a proof, ensure closed
      
    }
    break;
    // (reset)
    case Token::RESET:
    {
      //cmd.reset(new ResetCommand());
      // reset the state of the parser, which is independent of the symbol
      // manager
      d_state.reset();
    }
    break;
    // (set-info <attribute>)
    case Token::SET_INFO:
    {
      std::string key = d_eparser.parseKeyword();
      //Expr sexpr = d_eparser.parseSymbolicExpr();
      //cmd.reset(new SetInfoCommand(key, sexprToString(sexpr)));
    }
    break;
    // (set-logic <symbol>)
    case Token::SET_LOGIC:
    {
      std::string name = d_eparser.parseSymbol();
      // replace the logic with the forced logic, if applicable.
      //d_state.setLogic(lname);
      //cmd.reset(new SetBenchmarkLogicCommand(lname));
    }
    break;
    // (set-option <option>)
    case Token::SET_OPTION:
    {
      std::string key = d_eparser.parseKeyword();
      //Expr sexpr = d_eparser.parseSymbolicExpr();
      //std::string ss = sexprToString(sexpr);
      //cmd.reset(new SetOptionCommand(key, ss));
    }
    break;
    // (step ...)
    case Token::STEP:
    {
    }
    break;
    case Token::EOF_TOK:
      d_lex.parseError("Expected SMT-LIBv2 command", true);
      break;
    default:
      d_lex.unexpectedTokenError(tok, "Expected SMT-LIBv2 command");
      break;
  }
  d_lex.eatToken(Token::RPAREN);
  return true;
}

}  // namespace atc
