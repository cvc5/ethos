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
  d_table["declare-codatatypes"] = Token::DECLARE_CODATATYPES_TOK;
  d_table["declare-codatatype"] = Token::DECLARE_CODATATYPE_TOK;
  d_table["declare-const"] = Token::DECLARE_CONST_TOK;
  d_table["declare-datatypes"] = Token::DECLARE_DATATYPES_TOK;
  d_table["declare-datatype"] = Token::DECLARE_DATATYPE_TOK;
  d_table["declare-fun"] = Token::DECLARE_FUN_TOK;
  d_table["declare-sort"] = Token::DECLARE_SORT_TOK;
  d_table["define-const"] = Token::DEFINE_CONST_TOK;
  d_table["define-funs-rec"] = Token::DEFINE_FUNS_REC_TOK;
  d_table["define-fun-rec"] = Token::DEFINE_FUN_REC_TOK;
  d_table["define-fun"] = Token::DEFINE_FUN_TOK;
  d_table["define-sort"] = Token::DEFINE_SORT_TOK;
  d_table["echo"] = Token::ECHO_TOK;
  d_table["exit"] = Token::EXIT_TOK;
  d_table["pop"] = Token::POP_TOK;
  d_table["push"] = Token::PUSH_TOK;
  d_table["reset"] = Token::RESET_TOK;
  d_table["set-info"] = Token::SET_INFO_TOK;
  d_table["set-logic"] = Token::SET_LOGIC_TOK;
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
    // single datatype
    // (declare-datatype <symbol> <datatype_dec>)
    // (declare-codatatype <symbol> <datatype_dec>)
    /*
    case Token::DECLARE_CODATATYPE_TOK:
    case Token::DECLARE_DATATYPE_TOK:
    {
      d_state.checkThatLogicIsSet();
      std::vector<std::string> dnames;
      std::vector<size_t> arities;
      std::string name = d_eparser.parseSymbol(CHECK_UNDECLARED, SYM_SORT);
      dnames.push_back(name);
      bool isCo = (tok == Token::DECLARE_CODATATYPE_TOK);
      // parse <datatype_dec>
      std::vector<DatatypeDecl> dts =
          d_eparser.parseDatatypesDef(isCo, dnames, arities);
      cmd.reset(
          new DatatypeDeclarationCommand(d_state.mkMutualDatatypeTypes(dts)));
    }
    break;
    // multiple datatype
    // (declare-datatypes (<sort_dec>^{n+1}) (<datatype_dec>^{n+1}) )
    // (declare-codatatypes (<sort_dec>^{n+1}) (<datatype_dec>^{n+1}) )
    case Token::DECLARE_CODATATYPES_TOK:
    case Token::DECLARE_DATATYPES_TOK:
    {
      d_state.checkThatLogicIsSet();
      d_lex.eatToken(Token::LPAREN_TOK);
      std::vector<std::string> dnames;
      std::vector<size_t> arities;
      // parse (<sort_dec>^{n+1})
      // while the next token is LPAREN, exit if RPAREN
      while (d_lex.eatTokenChoice(Token::LPAREN_TOK, Token::RPAREN_TOK))
      {
        std::string name = d_eparser.parseSymbol(CHECK_UNDECLARED, SYM_SORT);
        size_t arity = d_eparser.parseIntegerNumeral();
        dnames.push_back(name);
        arities.push_back(arity);
        d_lex.eatToken(Token::RPAREN_TOK);
      }
      if (dnames.empty())
      {
        d_lex.parseError("Empty list of datatypes");
      }
      bool isCo = (tok == Token::DECLARE_CODATATYPES_TOK);
      // parse (<datatype_dec>^{n+1})
      d_lex.eatToken(Token::LPAREN_TOK);
      std::vector<DatatypeDecl> dts =
          d_eparser.parseDatatypesDef(isCo, dnames, arities);
      d_lex.eatToken(Token::RPAREN_TOK);
      cmd.reset(
          new DatatypeDeclarationCommand(d_state.mkMutualDatatypeTypes(dts)));
    }
    break;
    */
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
      //cmd.reset(new DeclareFunctionCommand(name, t));
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
    }
    break;
    // TODO (declare-type <symbol> ...)
    // (declare-var <symbol> <sort>)
    case Token::DECLARE_VAR_TOK:
    {
      //d_state.checkThatLogicIsSet();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      Expr t = d_eparser.parseExpr();
      //Expr var = d_state.getSolver()->declareSygusVar(name, t);
      //cmd.reset(new DeclareSygusVarCommand(name, var, t));
    }
    break;
    // (define-const <symbol> <sort> <term>)
    case Token::DEFINE_CONST_TOK:
    {
      //d_state.checkThatLogicIsSet();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      Expr t = d_eparser.parseExpr();
      Expr e = d_eparser.parseExpr();

      // declare the name down here (while parsing term, signature
      // must not be extended with the name itself; no recursion
      // permitted)
      //cmd.reset(new DefineFunctionCommand(name, t, e));
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
      /* add variables to parser state before parsing term */
      std::vector<Expr> sorts;
      if (sortedVarNames.size() > 0)
      {
        sorts.reserve(sortedVarNames.size());
        for (const std::pair<std::string, Expr>& i : sortedVarNames)
        {
          sorts.push_back(i.second);
        }
      }
      if (sortedVarNames.size() > 0)
      {
        d_state.pushScope();
      }
      std::vector<Expr> terms = d_state.bindBoundVars(sortedVarNames);
      Expr expr = d_eparser.parseExpr();
      if (sortedVarNames.size() > 0)
      {
        d_state.popScope();
      }
      //cmd.reset(new DefineFunctionCommand(name, terms, t, expr));
    }
    break;
    // (define-fun-rec <symbol> (<sorted_var>*) <sort> <term>)
    case Token::DEFINE_FUN_REC_TOK:
    {
      //d_state.checkThatLogicIsSet();
      std::string fname = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(fname);
      std::vector<std::pair<std::string, Expr>> sortedVarNames =
          d_eparser.parseSortedVarList();
      Expr t = d_eparser.parseExpr();
      std::vector<Expr> bvs;
      Expr func;
      // func =  d_state.bindDefineFunRec(fname, sortedVarNames, t);
      //d_state.pushDefineFunRecScope(sortedVarNames, func, bvs);
      Expr expr = d_eparser.parseExpr();
      d_state.popScope();
      //cmd.reset(new DefineFunctionRecCommand(func, bvs, expr));
    }
    break;
    // (define-funs-rec (<function_dec>^{n+1}) (<term>^{n+1}))
    // where
    // <function_dec> := (<symbol> (<sorted_var>*) <sort>)
    /*
    case Token::DEFINE_FUNS_REC_TOK:
    {
      //d_state.checkThatLogicIsSet();
      d_lex.eatToken(Token::LPAREN_TOK);
      std::vector<Expr> funcs;
      std::vector<std::vector<std::pair<std::string, Expr>>> sortedVarNamesList;
      // while the next token is LPAREN, exit if RPAREN
      // parse <function_dec>^{n+1}
      while (d_lex.eatTokenChoice(Token::LPAREN_TOK, Token::RPAREN_TOK))
      {
        std::string fname = d_eparser.parseSymbol();
        //d_state.checkUserSymbol(fname);
        std::vector<std::pair<std::string, Expr>> sortedVarNames =
            d_eparser.parseSortedVarList();
        Expr t = d_eparser.parseExpr();
        Expr func =
            d_state.bindDefineFunRec(fname, sortedVarNames, t, flattenVars);
        funcs.push_back(func);

        // add to lists (need to remember for when parsing the bodies)
        sortedVarNamesList.push_back(sortedVarNames);
        //flattenVarsList.push_back(flattenVars);
        d_lex.eatToken(Token::RPAREN_TOK);
      }

      // parse the bodies
      d_lex.eatToken(Token::LPAREN_TOK);
      std::vector<Expr> funcDefs;
      std::vector<std::vector<Expr>> formals;
      // parse <term>^{n+1}
      for (size_t j = 0, nfuncs = funcs.size(); j < nfuncs; j++)
      {
        std::vector<Expr> bvs;
        d_state.pushDefineFunRecScope(
            sortedVarNamesList[j], funcs[j], flattenVarsList[j], bvs);
        Expr expr = d_eparser.parseExpr();
        d_state.popScope();
        funcDefs.push_back(expr);
        formals.push_back(bvs);
      }
      d_lex.eatToken(Token::RPAREN_TOK);
      Assert(funcs.size() == funcDefs.size());
      //cmd.reset(new DefineFunctionRecCommand(funcs, formals, funcDefs));
    }
    break;
    */
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
      //cmd.reset(new DefineExprCommand(name, sorts, t));
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
      //cmd.reset(new QuitCommand());
      exit(0);
    }
    break;
    // (pop <numeral>?)
    case Token::POP_TOK:
    {
      // optional integer
      tok = d_lex.peekToken();
      if (tok == Token::INTEGER_LITERAL)
      {
        size_t num = d_eparser.parseIntegerNumeral();
        //cmd = d_state.handlePop(num);
      }
      else
      {
        //cmd = d_state.handlePop(std::nullopt);
      }
    }
    break;
    // (push <numeral>?)
    case Token::PUSH_TOK:
    {
      // optional integer
      tok = d_lex.peekToken();
      if (tok == Token::INTEGER_LITERAL)
      {
        size_t num = d_eparser.parseIntegerNumeral();
        //cmd = d_state.handlePush(num);
      }
      else
      {
        //cmd = d_state.handlePush(std::nullopt);
      }
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
      Expr sexpr = d_eparser.parseSymbolicExpr();
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
      Expr sexpr = d_eparser.parseSymbolicExpr();
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
