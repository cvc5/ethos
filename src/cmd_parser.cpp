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
#include <ostream>

namespace alfc {

CmdParser::CmdParser(Lexer& lex,
                             State& state,
                             ExprParser& eparser)
    : d_lex(lex), d_state(state), d_eparser(eparser), d_isFinished(false)
{
  // initialize the command tokens
  d_table["assume"] = Token::ASSUME;
  d_table["declare-codatatype"] = Token::DECLARE_CODATATYPE;
  d_table["declare-codatatypes"] = Token::DECLARE_CODATATYPES;
  d_table["declare-const"] = Token::DECLARE_CONST;
  d_table["declare-consts"] = Token::DECLARE_CONSTS;
  d_table["declare-datatype"] = Token::DECLARE_DATATYPE;
  d_table["declare-datatypes"] = Token::DECLARE_DATATYPES;
  d_table["declare-fun"] = Token::DECLARE_FUN;
  d_table["declare-rule"] = Token::DECLARE_RULE;
  d_table["declare-sort"] = Token::DECLARE_SORT;
  d_table["declare-type"] = Token::DECLARE_TYPE;
  d_table["declare-var"] = Token::DECLARE_VAR;
  d_table["define-const"] = Token::DEFINE_CONST;
  d_table["define-fun"] = Token::DEFINE_FUN;
  d_table["define-type"] = Token::DEFINE_TYPE;
  d_table["define-sort"] = Token::DEFINE_SORT;
  d_table["echo"] = Token::ECHO;
  d_table["exit"] = Token::EXIT;
  d_table["include"] = Token::INCLUDE;
  d_table["pop"] = Token::POP;
  d_table["program"] = Token::PROGRAM;
  d_table["proof"] = Token::PROOF;
  d_table["push"] = Token::PUSH;
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
  if (d_isFinished || d_lex.eatTokenChoice(Token::EOF_TOK, Token::LPAREN))
  {
    return false;
  }
  Token tok = nextCommandToken();
  switch (tok)
  {
    // (assume <symbol> <term>)
    // (push <symbol> <term>)
    case Token::ASSUME:
    case Token::PUSH:
    {
      if (tok==Token::PUSH)
      {
        d_state.pushAssumptionScope();
      }
      std::string name = d_eparser.parseSymbol();
      // parse what is proven
      Expr proven = d_eparser.parseFormula();
      Expr pt = d_state.mkProofType(proven);
      Expr v = d_state.mkConst(name, pt);
      d_eparser.bind(name, v);
      d_state.addAssumption(proven);
    }
    break;
    // (declare-fun <symbol> (<sort>∗) <sort>)
    // (declare-const <symbol> <sort>)
    // (declare-var <symbol> <sort>)
    case Token::DECLARE_CONST:
    case Token::DECLARE_FUN:
    case Token::DECLARE_VAR:
    {
      //d_state.checkThatLogicIsSet();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      std::vector<Expr> sorts;
      if (tok == Token::DECLARE_FUN)
      {
        sorts = d_eparser.parseExprList();
      }
      Expr t = d_eparser.parseType();
      if (!sorts.empty())
      {
        t = d_state.mkFunctionType(sorts, t);
      }
      Expr v;
      if (tok == Token::DECLARE_VAR)
      {
        v = d_state.mkParameter(name, t);
      }
      else
      {
        v = d_state.mkConst(name, t);
      }
      d_eparser.bind(name, v);
      // possible attribute list
      AttrMap attrs;
      d_eparser.parseAttributeList(v, attrs);
      d_state.markAttributes(v, attrs);
    }
    break;
    // single datatype
    // (declare-datatype <symbol> <datatype_dec>)
    // (declare-codatatype <symbol> <datatype_dec>)
    case Token::DECLARE_CODATATYPE:
    case Token::DECLARE_DATATYPE:
    {
      //d_state.checkThatLogicIsSet();
      std::vector<std::string> dnames;
      std::vector<size_t> arities;
      std::string name = d_eparser.parseSymbol();
      dnames.push_back(name);
      //bool isCo = (tok == Token::DECLARE_CODATATYPE);
      std::map<Expr, std::vector<Expr>> dts;
      std::map<Expr, std::vector<Expr>> dtcons;
      // parse <datatype_dec>
      d_eparser.parseDatatypesDef(dnames, arities, dts, dtcons);
    }
    break;
    // multiple datatype
    // (declare-datatypes (<sort_dec>^{n+1}) (<datatype_dec>^{n+1}) )
    // (declare-codatatypes (<sort_dec>^{n+1}) (<datatype_dec>^{n+1}) )
    case Token::DECLARE_CODATATYPES:
    case Token::DECLARE_DATATYPES:
    {
      //d_state.checkThatLogicIsSet();
      d_lex.eatToken(Token::LPAREN);
      std::vector<std::string> dnames;
      std::vector<size_t> arities;
      // parse (<sort_dec>^{n+1})
      // while the next token is LPAREN, exit if RPAREN
      while (d_lex.eatTokenChoice(Token::LPAREN, Token::RPAREN))
      {
        std::string name = d_eparser.parseSymbol();
        size_t arity = d_eparser.parseIntegerNumeral();
        dnames.push_back(name);
        arities.push_back(arity);
        d_lex.eatToken(Token::RPAREN);
      }
      if (dnames.empty())
      {
        d_lex.parseError("Empty list of datatypes");
      }
      //bool isCo = (tok == Token::DECLARE_CODATATYPES);
      // parse (<datatype_dec>^{n+1})
      d_lex.eatToken(Token::LPAREN);
      std::map<Expr, std::vector<Expr>> dts;
      std::map<Expr, std::vector<Expr>> dtcons;
      d_eparser.parseDatatypesDef(dnames, arities, dts, dtcons);
      d_lex.eatToken(Token::RPAREN);
    }
    break;
    // (declare-consts <symbol> <sort>)
    case Token::DECLARE_CONSTS:
    {
      Kind k = d_eparser.parseLiteralKind();
      Expr t = d_eparser.parseType();
      // set the type rule
      d_state.setLiteralTypeRule(k, t);
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
      Expr assume;
      if (keyword=="assumption")
      {
        assume = d_eparser.parseExpr();
        keyword = d_eparser.parseKeyword();
      }
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
      if (assume!=nullptr)
      {
        Expr ast = d_state.mkQuoteType(assume);
        argTypes.push_back(ast);
      }
      for (const Expr& e : premises)
      {
        Expr pet = d_state.mkProofType(e);
        argTypes.push_back(pet);
      }
      for (Expr& e : args)
      {
        Expr et = d_state.mkQuoteType(e);
        argTypes.push_back(et);
      }
      Expr ret = d_state.mkProofType(conc);
      // include the requirements into the return type
      if (!reqs.empty())
      {
        ret = d_state.mkRequiresType(reqs, ret);
      }
      // Ensure all free variables in the conclusion are bound in the arguments.
      // Otherwise, this rule will always generate a free variable, which is
      // likely unintentional.
      std::vector<Expr> bvs = ExprValue::getVariables(argTypes);
      d_eparser.ensureBound(ret, bvs);
      // make the overall type
      if (!argTypes.empty())
      {
        ret = d_state.mkFunctionType(argTypes, ret, false);
      }
      d_state.popScope();
      Expr rule = d_state.mkProofRule(name, ret);
      d_eparser.typeCheck(rule);
      d_eparser.bind(name, rule);
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
      Expr decType = d_state.mkTypeConstant(name, arity);
      d_eparser.bind(name, decType);
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
      d_eparser.bind(name, decType);
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
      d_eparser.bind(name, e);
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
      d_eparser.bind(name, expr);
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
          Expr v = d_state.mkParameter(sname, ttype);
          d_eparser.bind(sname, v);
        }
      }
      Expr t = d_eparser.parseType();
      if (!snames.empty())
      {
        d_state.popScope();
      }
      d_eparser.bind(name, t);
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
      d_isFinished = true;
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
      // push the scope
      d_state.pushScope();
      std::vector<Expr> vars = d_eparser.parseAndBindSortedVarList();

      std::vector<Expr> argTypes = d_eparser.parseExprList();
      Expr retType = d_eparser.parseType();
      if (!argTypes.empty())
      {
        retType = d_state.mkFunctionType(argTypes, retType, false);
      }
      // the type of the program variable is a function
      Expr pvar = d_state.mkProgramConst(name, retType);
      // bind the program
      d_eparser.bind(name, pvar);
      // parse the body
      std::vector<Expr> pchildren = d_eparser.parseExprPairList();
      if (pchildren.empty())
      {
        d_lex.parseError("Expected non-empty list of cases");
      }
      // ensure program cases are
      // (A) applications of the program
      // (B) have arguments that are not evaluatable
      for (Expr& p : pchildren)
      {
        Expr pc = (*p.get())[0];
        if (pc->getKind()!=Kind::APPLY || pc->getChildren()[0]!=pvar)
        {
          d_lex.parseError("Expected application of program as case");
        }
        // ensure the right hand side is bound by the left hand side
        std::vector<Expr> bvs = ExprValue::getVariables(pc);
        Expr rhs = (*p.get())[1];
        d_eparser.ensureBound(rhs, bvs);
        // TODO: allow variable or default case?
        const std::vector<Expr>& children = pc->getChildren();
        for (const Expr& ec : children)
        {
          Expr ecc = ec;
          if (ecc->isEvaluatable())
          {
            std::stringstream ss;
            ss << "Cannot match on evaluatable subterm " << ec;
            d_lex.parseError(ss.str());
          }
        }
      }
      d_state.popScope();
      Expr program = d_state.mkExpr(Kind::PROGRAM, pchildren);
      d_state.defineProgram(pvar, program);
      // rebind the program
      d_eparser.bind(name, pvar);
    }
    break;
    // (proof <formula> <term>)
    // NOTE: doesn't allow optional
    case Token::PROOF:
    {
      Expr proven = d_eparser.parseExpr();
      Expr p = d_eparser.parseExpr();
      Expr pt = d_state.mkProofType(proven);
      // ensure a proof of the given fact
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
    // The parameters :premises and :args can be omitted if empty 
    case Token::STEP:
    case Token::POP:
    {
      bool isPop = (tok==Token::POP);
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
      Expr rule = d_eparser.getVar(ruleName);
      // parse premises, optionally
      if (d_lex.peekToken()==Token::KEYWORD)
      {
        keyword = d_eparser.parseKeyword();
      }
      std::vector<Expr> premises;
      if (keyword=="premises")
      {
        premises = d_eparser.parseExprList();
        if (d_lex.peekToken()==Token::KEYWORD)
        {
          keyword = d_eparser.parseKeyword();
        }
      }
      // parse args, optionally
      std::vector<Expr> args;
      if (keyword=="args")
      {
        args = d_eparser.parseExprList();
      }
      std::vector<Expr> children;
      children.push_back(rule);
      // the assumption, if pop
      if (isPop)
      {
        if (d_state.getAssumptionLevel()==0)
        {
          d_lex.parseError("Cannot pop at level zero");
        }
        std::vector<Expr> as = d_state.getCurrentAssumptions();
        Assert (as.size()==1);
        // push the assumption
        children.push_back(as[0]);
      }
      // premises before arguments
      children.insert(children.end(), premises.begin(), premises.end());
      for (const Expr& e : args)
      {
        children.push_back(e);
      }
      // compute the type of applying the rule
      Expr concType;
      if (children.size()>1)
      {
        // check type rule for APPLY directly without constructing the app
        concType = d_state.getTypeChecker().getTypeApp(children);
      }
      else
      {
        concType = d_state.getTypeChecker().getType(rule);
      }
      // ensure proof type, note this is where "proof checking" happens.
      if (concType->getKind()!=Kind::PROOF_TYPE)
      {
        std::stringstream ss;
        ss << "Non-proof conclusion for step, got " << concType;
        d_lex.parseError(ss.str());
      }
      if (proven!=nullptr)
      {
        Expr& actual = concType->getChildren()[0];
        if (actual!=proven)
        {
          std::stringstream ss;
          ss << "Unexpected conclusion for step:" << std::endl;
          ss << "    Proves: " << actual << std::endl;
          ss << "  Expected: " << proven;
          d_lex.parseError(ss.str());
        }
      }
      // bind to variable, note that the definition term is not kept
      Expr v = d_state.mkConst(name, concType);
      d_eparser.bind(name, v);
      // d_eparser.bind(name, def);
      if (isPop)
      {
        d_state.popAssumptionScope();
      }
    }
    break;
    case Token::EOF_TOK:
      d_lex.parseError("Expected AletheLF command", true);
      break;
    default:
      d_lex.unexpectedTokenError(tok, "Expected AletheLF command");
      break;
  }
  d_lex.eatToken(Token::RPAREN);
  return true;
}

}  // namespace alfc
