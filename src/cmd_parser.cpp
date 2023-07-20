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
  d_table["declare-consts"] = Token::DECLARE_CONSTS;
  d_table["declare-fun"] = Token::DECLARE_FUN;
  d_table["declare-rule"] = Token::DECLARE_RULE;
  d_table["declare-sort"] = Token::DECLARE_SORT;
  d_table["declare-type"] = Token::DECLARE_TYPE;
  d_table["define-const"] = Token::DEFINE_CONST;
  d_table["define-fun"] = Token::DEFINE_FUN;
  d_table["define-type"] = Token::DEFINE_TYPE;
  d_table["define-sort"] = Token::DEFINE_SORT;
  d_table["echo"] = Token::ECHO;
  d_table["exit"] = Token::EXIT;
  d_table["include"] = Token::INCLUDE;
  d_table["program"] = Token::PROGRAM;
  d_table["proof"] = Token::PROOF;
  d_table["reset"] = Token::RESET;
  d_table["set-info"] = Token::SET_INFO;
  d_table["set-option"] = Token::SET_OPTION;
  d_table["step"] = Token::STEP;
  
  d_symbolLitNames["<numeral>"] = Kind::INTEGER;
  d_symbolLitNames["<decimal>"] = Kind::DECIMAL;
  d_symbolLitNames["<hexadecimal>"] = Kind::HEXADECIMAL;
  d_symbolLitNames["<binary>"] = Kind::BINARY;
  d_symbolLitNames["<string>"] = Kind::STRING;
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
      Expr pt = d_state.mkProofType(proven);
      Expr v = d_state.mkConst(name, pt);
      bind(name, v);
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
      bind(name, v);
    }
    break;
    // (declare-consts <symbol> <sort>)
    case Token::DECLARE_CONSTS:
    {
      std::string name = d_eparser.parseSymbol();
      Expr t = d_eparser.parseType();
      std::map<std::string, Kind>::iterator it = d_symbolLitNames.find(name);
      if (it==d_symbolLitNames.end())
      {
        d_lex.parseError("Unknown category for declare-consts");
      }
      // set the type rule
      d_state.getTypeChecker().setTypeRule(it->second, t);
    }
    break;
    // (declare-rule ...)
    case Token::DECLARE_RULE:
    {
      d_state.pushScope();
      std::string name = d_eparser.parseSymbol();
      std::vector<Expr> vs =
          d_eparser.parseAndBindSortedVarList();
      // parse premises, optionally
      std::string keyword = d_eparser.parseKeyword();
      std::vector<Expr> premises;
      if (keyword=="premises")
      {
        premises = d_eparser.parseExprList();
        keyword = d_eparser.parseKeyword();
      }
      // parse args, optionally
      std::vector<Expr> args;
      if (keyword=="args")
      {
        args = d_eparser.parseExprList();
        keyword = d_eparser.parseKeyword();
      }
      // parse requirements, optionally
      std::vector<Expr> reqs;
      if (keyword=="requires")
      {
        reqs = d_eparser.parseExprPairList();
        keyword = d_eparser.parseKeyword();
      }
      // parse conclusion
      if (keyword!="conclusion")
      {
        d_lex.parseError("Expected conclusion in declare-rule");
      }
      Expr conc = d_eparser.parseExpr();
      std::vector<Expr> argTypes;
      for (Expr& e : args)
      {
        Expr et = d_state.mkQuoteType(e);
        argTypes.push_back(et);
      }
      for (const Expr& e : premises)
      {
        Expr pet = d_state.mkProofType(e);
        argTypes.push_back(pet);
      }
      Expr ret = d_state.mkProofType(conc);
      // include the requirements into the return type
      if (!reqs.empty())
      {
        ret = d_state.mkRequiresType(reqs, ret);
      }
      if (!argTypes.empty())
      {
        ret = d_state.mkFunctionType(argTypes, ret);
      }
      d_state.popScope();
      Expr rule = d_state.mkConst(name, ret);
      d_eparser.typeCheck(rule);
      bind(name, rule);
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
      bind(name, decType);
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
        type = d_state.mkFunctionType(args, ttype);
      }
      Expr decType = d_state.mkConst(name, type);
      bind(name, decType);
    }
    break;
    // (define-const <symbol> <sort> <term>)
    case Token::DEFINE_CONST:
    {
      //d_state.checkThatLogicIsSet();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      Expr ret = d_eparser.parseType();
      Expr e = d_eparser.parseExpr();
      d_eparser.typeCheck(e, ret);
      bind(name, e);
    }
    break;
    // (define-fun <symbol> (<sorted_var>*) <sort> <term>)
    // (define-type <symbol> (<sorted_var>*) <term>)
    case Token::DEFINE_FUN:
    case Token::DEFINE_TYPE:
    {
      d_state.pushScope();
      //d_state.checkThatLogicIsSet();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      std::vector<Expr> vars =
          d_eparser.parseAndBindSortedVarList();
      Expr ret;
      if (tok == Token::DEFINE_FUN)
      {
        ret = d_eparser.parseType();
      }
      else
      {
        ret = d_state.mkType();
      }
      Expr expr = d_eparser.parseExpr();
      // ensure we have the right type
      d_eparser.typeCheck(expr, ret);
      d_state.popScope();
      // make a lambda if given arguments
      if (vars.size() > 0)
      {
        Expr vl = d_state.mkExpr(Kind::VARIABLE_LIST, vars);
        expr = d_state.mkExpr(Kind::LAMBDA, {vl, expr});
      }
      bind(name, expr);
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
          bind(sname, v);
        }
      }
      Expr t = d_eparser.parseType();
      if (!snames.empty())
      {
        d_state.popScope();
      }
      bind(name, t);
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
      if (tok != Token::STRING_LITERAL)
      {
        d_lex.parseError("Expected string literal for include");
      }
      // include the file
      std::string msg = d_eparser.parseStr(true);
      d_state.includeFile(msg);
    }
    break;
    // (program (<sort>*) <sort> (<sorted_var>*) <term_pair>+)
    case Token::PROGRAM:
    {
      std::string name = d_eparser.parseSymbol();
      std::vector<Expr> argTypes = d_eparser.parseExprList();
      Expr retType = d_eparser.parseType();
      if (!argTypes.empty())
      {
        retType = d_state.mkFunctionType(argTypes, retType);
      }
      // the type of the program variable is a function
      Expr pvar = d_state.mkConst(name, retType);
      // bind the program prior to pushing the scope
      bind(name, pvar);
      // push the scope
      d_state.pushScope();
      std::vector<Expr> vars = d_eparser.parseAndBindSortedVarList();
      // parse the body
      std::vector<Expr> pchildren = d_eparser.parseExprPairList();
      if (pchildren.empty())
      {
        d_lex.parseError("Expected non-empty list of cases");
      }
      d_state.popScope();
      Expr program = d_state.mkExpr(Kind::PROGRAM, pchildren);
      d_state.defineProgram(pvar, program);
    }
    break;
    // (proof <formula> <term>)
    case Token::PROOF:
    {
      Expr proven = d_eparser.parseExpr();
      Expr p = d_eparser.parseExpr();
      Expr pt = d_state.mkProofType(proven);
      // ensure a proof of the given fact, ensure closed
      d_eparser.typeCheck(p, pt);
    }
    break;
    // (reset)
    case Token::RESET:
    {
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
    // (step i F? :rule R :premises (p1 ... pn) :args (t1 ... tm))
    // which is syntax sugar for
    // (define-const i (Proof F) (R t1 ... tm p1 ... pn))
    case Token::STEP:
    {
      std::string name = d_eparser.parseSymbol();
      Expr proven;
      // see if we have proven
      tok = d_lex.peekToken();
      if (tok != Token::KEYWORD)
      {
        proven = d_eparser.parseExpr();
      }
      // parse rule name
      std::string keyword = d_eparser.parseKeyword();
      if (keyword!="rule")
      {
        d_lex.parseError("Expected rule in step");
      }
      std::string ruleName = d_eparser.parseSymbol();
      Expr rule = d_state.getVar(ruleName);
      // parse premises
      keyword = d_eparser.parseKeyword();
      if (keyword!="premises")
      {
        d_lex.parseError("Expected premises in step");
      }
      std::vector<Expr> premises = d_eparser.parseExprList();
      // parse args
      keyword = d_eparser.parseKeyword();
      if (keyword!="args")
      {
        d_lex.parseError("Expected args in step");
      }
      std::vector<Expr> args = d_eparser.parseExprList();
      std::vector<Expr> children;
      children.push_back(rule);
      // args before premises
      for (const Expr& e : args)
      {
        children.push_back(d_state.mkExpr(Kind::QUOTE, {e}));
      }
      children.insert(children.end(), premises.begin(), premises.end());
      Expr def = d_state.mkExpr(Kind::APPLY, children);
      // ensure proof type, note this is where "proof checking" happens.
      if (proven!=nullptr)
      {
        Expr expected = d_state.mkProofType(proven);
        d_eparser.typeCheck(def, expected);
      }
      // bind
      bind(name, def);
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

void CmdParser::bind(const std::string& name, const Expr& e)
{
  if (!d_state.bind(name, e))
  {
    std::stringstream ss;
    ss << "Failed to bind symbol " << name;
    d_lex.parseError(ss.str());
  }
}

}  // namespace atc
