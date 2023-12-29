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
#include "base/output.h"

namespace alfc {

CmdParser::CmdParser(Lexer& lex,
                     State& state,
                     ExprParser& eparser,
                     bool isReference)
    : d_lex(lex), d_state(state), d_eparser(eparser), d_isReference(isReference), d_isFinished(false)
{
  // initialize the command tokens

  // commands supported in both inputs and proofs
  d_table["declare-codatatype"] = Token::DECLARE_CODATATYPE;
  d_table["declare-codatatypes"] = Token::DECLARE_CODATATYPES;
  d_table["declare-const"] = Token::DECLARE_CONST;
  d_table["declare-datatype"] = Token::DECLARE_DATATYPE;
  d_table["declare-datatypes"] = Token::DECLARE_DATATYPES;
  d_table["declare-fun"] = Token::DECLARE_FUN;
  d_table["declare-oracle-fun"] = Token::DECLARE_ORACLE_FUN;
  d_table["declare-sort"] = Token::DECLARE_SORT;
  d_table["define-const"] = Token::DEFINE_CONST;
  d_table["define-fun"] = Token::DEFINE_FUN;
  d_table["define-sort"] = Token::DEFINE_SORT;
  d_table["echo"] = Token::ECHO;
  d_table["exit"] = Token::EXIT;
  d_table["reset"] = Token::RESET;

  if (d_isReference)
  {
    // only used in smt2 queries
    d_table["assert"] = Token::ASSERT;
    d_table["check-sat"] = Token::CHECK_SAT;
    d_table["check-sat-assuming"] = Token::CHECK_SAT_ASSUMING;
    d_table["set-logic"] = Token::SET_LOGIC;
    d_table["set-info"] = Token::SET_INFO;
    d_table["set-option"] = Token::SET_OPTION;
  }
  else
  {
    // not defined in smt 2.6, or not supported
    d_table["assume"] = Token::ASSUME;
    d_table["assume-push"] = Token::ASSUME_PUSH;
    d_table["declare-axiom"] = Token::DECLARE_AXIOM;
    d_table["declare-consts"] = Token::DECLARE_CONSTS;
    d_table["declare-rule"] = Token::DECLARE_RULE;
    d_table["declare-type"] = Token::DECLARE_TYPE;
    d_table["declare-var"] = Token::DECLARE_VAR;
    d_table["define"] = Token::DEFINE;
    d_table["define-type"] = Token::DEFINE_TYPE;
    d_table["include"] = Token::INCLUDE;
    d_table["program"] = Token::PROGRAM;
    d_table["reference"] = Token::REFERENCE;
    d_table["step"] = Token::STEP;
    d_table["step-pop"] = Token::STEP_POP;
  }
  
  d_statsEnabled = d_state.getOptions().d_stats;
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
    case Token::ASSUME_PUSH:
    {
      if (tok==Token::ASSUME_PUSH)
      {
        d_state.pushAssumptionScope();
      }
      std::string name = d_eparser.parseSymbol();
      // parse what is proven
      Expr proven = d_eparser.parseFormula();
      Expr pt = d_state.mkProofType(proven);
      Expr v = d_state.mkSymbol(Kind::CONST, name, pt);
      d_eparser.bind(name, v);
      if (!d_state.addAssumption(proven))
      {
        std::stringstream ss;
        ss << "The assumption " << name << " was not part of the referenced assertions";
        d_lex.parseError(ss.str());
      }
    }
    break;
    // (declare-fun <symbol> (<sort>∗) <sort>)
    // (declare-oracle-fun <symbol> (<sort>∗) <sort>)
    // (declare-const <symbol> <sort>)
    // (declare-var <symbol> <sort>)
    case Token::DECLARE_CONST:
    case Token::DECLARE_FUN:
    case Token::DECLARE_ORACLE_FUN:
    case Token::DECLARE_VAR:
    {
      //d_state.checkThatLogicIsSet();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      std::vector<Expr> sorts;
      bool flattenFunction = (tok != Token::DECLARE_ORACLE_FUN);
      if (tok == Token::DECLARE_FUN || tok == Token::DECLARE_ORACLE_FUN)
      {
        sorts = d_eparser.parseTypeList();
      }
      Expr t = d_eparser.parseType();
      if (!sorts.empty())
      {
        t = d_state.mkFunctionType(sorts, t, flattenFunction);
      }
      Attr ck = Attr::NONE;
      Expr cons;
      Kind sk;
      if (tok==Token::DECLARE_ORACLE_FUN)
      {
        ck = Attr::ORACLE;
        sk = Kind::ORACLE;
        std::string oname = d_eparser.parseSymbol();
        cons = d_state.mkLiteral(Kind::STRING, oname);
      }
      else if (tok==Token::DECLARE_CONST || tok==Token::DECLARE_FUN)
      {
        sk = Kind::CONST;
        // possible attribute list
        AttrMap attrs;
        d_eparser.parseAttributeList(t, attrs);
        // determine if an attribute specified a constructor kind
        if (d_eparser.processAttributeMap(attrs, ck, cons))
        {
          // if so, this may transform the type
          t = d_state.mkAnnotatedType(t, ck, cons);
        }
      }
      else
      {
        sk = Kind::VARIABLE;
        // don't permit attributes for variables
      }
      Expr v = d_state.mkSymbol(sk, name, t);
      // if the type has a property, we mark it on the variable of this type
      if (ck!=Attr::NONE)
      {
        if (!d_state.markConstructorKind(v, ck, cons))
        {
          std::stringstream ss;
          ss << "Failed to mark " << v << " with attribute " << ck;
          d_lex.parseError(ss.str());
        }
      }
      // bind
      d_eparser.bind(name, v);
    }
    break;
    // single or multiple datatype
    // (declare-datatype <symbol> <datatype_dec>)
    // (declare-codatatype <symbol> <datatype_dec>)
    // (declare-datatypes (<sort_dec>^{n+1}) (<datatype_dec>^{n+1}) )
    // (declare-codatatypes (<sort_dec>^{n+1}) (<datatype_dec>^{n+1}) )
    case Token::DECLARE_CODATATYPE:
    case Token::DECLARE_DATATYPE:
    case Token::DECLARE_CODATATYPES:
    case Token::DECLARE_DATATYPES:
    {
      bool isCo = (tok==Token::DECLARE_CODATATYPES || tok==Token::DECLARE_CODATATYPE);
      bool isMulti = (tok==Token::DECLARE_CODATATYPES || tok==Token::DECLARE_DATATYPES);
      //d_state.checkThatLogicIsSet();
      d_lex.eatToken(Token::LPAREN);
      std::vector<std::string> dnames;
      std::vector<size_t> arities;
      std::map<const ExprValue*, std::vector<Expr>> dts;
      std::map<const ExprValue*, std::vector<Expr>> dtcons;
      if (isMulti)
      {
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
        // parse (<datatype_dec>^{n+1})
        d_lex.eatToken(Token::LPAREN);
      }
      else
      {
        std::string name = d_eparser.parseSymbol();
        dnames.push_back(name);
      }
      if (!d_eparser.parseDatatypesDef(dnames, arities, dts, dtcons))
      {
        d_lex.parseError("Failed to bind symbols for datatype definition");
      }
      // mark the attributes
      Attr attr = isCo ? Attr::CODATATYPE : Attr::DATATYPE;
      for (std::pair<const ExprValue* const, std::vector<Expr>>& d : dts)
      {
        Expr dt = Expr(d.first);
        Expr ctuple = d_state.mkExpr(Kind::TUPLE, d.second);
        d_state.markConstructorKind(dt, attr, ctuple);
      }
      for (std::pair<const ExprValue* const, std::vector<Expr>>& c : dtcons)
      {
        Expr cons = Expr(c.first);
        Expr stuple = d_state.mkExpr(Kind::TUPLE, c.second);
        d_state.markConstructorKind(cons, Attr::DATATYPE_CONSTRUCTOR, stuple);
      }
      d_lex.eatToken(Token::RPAREN);
    }
    break;
    // (declare-consts <symbol> <sort>)
    case Token::DECLARE_CONSTS:
    {
      Kind k = d_eparser.parseLiteralKind();
      Expr t = d_eparser.parseType();
      // maybe requires?
      // set the type rule
      d_state.setLiteralTypeRule(k, t);
    }
    break;
    // (declare-rule ...)
    case Token::DECLARE_RULE:
    case Token::DECLARE_AXIOM:
    {
      // ensure zero scope
      if (d_state.getAssumptionLevel()>0)
      {
        d_lex.parseError("Rules must be declared at assumption level zero");
      }
      d_state.pushScope();
      std::string name = d_eparser.parseSymbol();
      std::vector<Expr> vs =
          d_eparser.parseAndBindSortedVarList();
      Expr assume;
      Expr plCons;
      std::vector<Expr> premises;
      std::vector<Expr> args;
      std::vector<Expr> reqs;
      Expr conc;
      bool matchConclusion = false;
      if (tok==Token::DECLARE_RULE)
      {
        // parse premises, optionally
        std::string keyword = d_eparser.parseKeyword();
        if (keyword=="assumption")
        {
          assume = d_eparser.parseExpr();
          keyword = d_eparser.parseKeyword();
        }
        if (keyword=="premises")
        {
          premises = d_eparser.parseExprList();
          keyword = d_eparser.parseKeyword();
        }
        else if (keyword=="premise-list")
        {
          // :premise-list <pattern> <cons>
          Expr pat = d_eparser.parseExpr();
          plCons = d_eparser.parseExpr();
          // pattern is the single premise
          premises.push_back(pat);
          keyword = d_eparser.parseKeyword();
        }
        // parse args, optionally
        if (keyword=="args")
        {
          args = d_eparser.parseExprList();
          keyword = d_eparser.parseKeyword();
        }
        // parse requirements, optionally
        if (keyword=="requires")
        {
          reqs = d_eparser.parseExprPairList();
          keyword = d_eparser.parseKeyword();
        }
        // parse conclusion
        if (keyword != "conclusion" && keyword != "match-conclusion")
        {
          d_lex.parseError(
              "Expected conclusion or match-conclusion in declare-rule");
        }
        matchConclusion = (keyword == "match-conclusion");
        conc = d_eparser.parseExpr();
      }
      else
      {
        // arguments are the parameters
        args.insert(args.end(), vs.begin(), vs.end());
        conc = d_eparser.parseExpr();
      }
      std::vector<Expr> argTypes;
      if (!assume.isNull())
      {
        Expr ast = d_state.mkQuoteType(assume);
        argTypes.push_back(ast);
      }
      for (const Expr& e : premises)
      {
        Expr pet = d_state.mkProofType(e);
        argTypes.push_back(pet);
      }
      if (matchConclusion)
      {
        Expr et = d_state.mkQuoteType(conc);
        argTypes.push_back(et);
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
        ret = d_state.mkRequires(reqs, ret);
      }
      // Ensure all free variables in the conclusion are bound in the arguments.
      // Otherwise, this rule will always generate a free variable, which is
      // likely unintentional.
      std::vector<Expr> bvs = Expr::getVariables(argTypes);
      d_eparser.ensureBound(ret, bvs);
      // make the overall type
      if (!argTypes.empty())
      {
        ret = d_state.mkFunctionType(argTypes, ret, false);
      }
      d_state.popScope();
      Expr rule = d_state.mkSymbol(Kind::PROOF_RULE, name, ret);
      d_eparser.typeCheck(rule);
      d_eparser.bind(name, rule);
      if (!plCons.isNull())
      {
        if (matchConclusion)
        {
          d_state.markConstructorKind(
              rule, Attr::PREMISE_LIST_MATCH_CONCLUSION, plCons);
        }
        else
        {
          d_state.markConstructorKind(rule, Attr::PREMISE_LIST, plCons);
        }
      }
      else
      {
        if (matchConclusion)
        {
          d_state.markConstructorKind(
              rule, Attr::MATCH_CONCLUSION, d_state.mkNil());
        }
      }
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
      std::vector<Expr> args = d_eparser.parseTypeList();
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
      Expr decType = d_state.mkSymbol(Kind::CONST, name, type);
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
    // (define <symbol> (<sorted_var>*) <term>)
    case Token::DEFINE_FUN:
    case Token::DEFINE_TYPE:
    case Token::DEFINE:
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
      else if (tok == Token::DEFINE_TYPE)
      {
        ret = d_state.mkType();
      }
      Expr expr = d_eparser.parseExpr();
      // ensure we have the right type
      if (!ret.isNull())
      {
        d_eparser.typeCheck(expr, ret);
      }
      d_state.popScope();
      // make a lambda if given arguments
      if (vars.size() > 0)
      {
        Expr vl = d_state.mkExpr(Kind::TUPLE, vars);
        expr = d_state.mkExpr(Kind::LAMBDA, {vl, expr});
      }
      d_eparser.bind(name, expr);
      Trace("define") << "Define: " << name << " -> " << expr << std::endl;
    }
    break;
    // (define-sort <symbol> (<symbol>*) <sort>)
    case Token::DEFINE_SORT:
    {
      //d_state.checkThatLogicIsSet();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      std::vector<Expr> vars;
      std::vector<std::string> snames =
          d_eparser.parseSymbolList();
      if (!snames.empty())
      {
        d_state.pushScope();
        std::vector<Expr> sorts;
        Expr ttype = d_state.mkType();
        for (const std::string& sname : snames)
        {
          Expr v = d_state.mkSymbol(Kind::PARAM, sname, ttype);
          d_eparser.bind(sname, v);
          vars.push_back(v);
        }
      }
      Expr t = d_eparser.parseType();
      if (!snames.empty())
      {
        d_state.popScope();
        Expr vl = d_state.mkExpr(Kind::TUPLE, vars);
        t = d_state.mkExpr(Kind::LAMBDA, {vl, t});
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
    case Token::REFERENCE:
    {
      bool isReference = (tok==Token::REFERENCE);
      if (isReference)
      {
        if (d_state.hasReference())
        {
          d_lex.parseError("Cannot use more than one reference");
        }
        if (d_state.getOptions().d_compile)
        {
          d_lex.parseError("Cannot use reference when compiling");
        }
      }
      if (d_state.getAssumptionLevel()>0)
      {
        d_lex.parseError("Includes must be done at assumption level zero");
      }
      tok = d_lex.peekToken();
      if (tok != Token::STRING_LITERAL)
      {
        d_lex.parseError("Expected string literal for include");
      }
      // include the file
      std::string file = d_eparser.parseStr(true);
      // read the optional reference normalize function
      Expr referenceNf;
      if (isReference && d_lex.peekToken()!=Token::RPAREN)
      {
        referenceNf = d_eparser.parseExpr();
      }
      if (!d_state.includeFile(file, isReference, referenceNf))
      {
        std::stringstream ss;
        ss << "Cannot include file " << file;
        d_lex.parseError(ss.str());
      }
    }
    break;
    // (program (<sort>*) <sort> (<sorted_var>*) <term_pair>+)
    case Token::PROGRAM:
    {
      std::string name = d_eparser.parseSymbol();
      // push the scope
      d_state.pushScope();
      std::vector<Expr> vars = d_eparser.parseAndBindSortedVarList();
      std::vector<Expr> argTypes = d_eparser.parseTypeList();
      Expr retType = d_eparser.parseType();
      Expr progType = retType;
      if (!argTypes.empty())
      {
        progType = d_state.mkFunctionType(argTypes, retType, false);
      }
      // the type of the program variable is a function
      Expr pvar = d_state.mkSymbol(Kind::PROGRAM_CONST, name, progType);
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
        Expr pc = p[0];
        if (pc.getKind() != Kind::APPLY || pc[0] != pvar)
        {
          d_lex.parseError("Expected application of program as case");
        }
        if (pc.getNumChildren() != argTypes.size() + 1)
        {
          d_lex.parseError("Wrong arity for pattern");
        }
        // ensure some type checking??
        //d_eparser.typeCheck(pc);
        // ensure the right hand side is bound by the left hand side
        std::vector<Expr> bvs = Expr::getVariables(pc);
        Expr rhs = p[1];
        d_eparser.ensureBound(rhs, bvs);
        // TODO: allow variable or default case?
        for (size_t i = 0, nchildren = pc.getNumChildren(); i < nchildren; i++)
        {
          Expr ecc = pc[i];
          if (ecc.isEvaluatable())
          {
            std::stringstream ss;
            ss << "Cannot match on evaluatable subterm " << pc[i];
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
    // (reset)
    case Token::RESET:
    {
      // reset the state of the parser, which is independent of the symbol
      // manager
      d_state.reset();
    }
    break;
    // (step i F? :rule R :premises (p1 ... pn) :args (t1 ... tm))
    // which is syntax sugar for
    // (define-const i (Proof F) (R t1 ... tm p1 ... pn))
    // The parameters :premises and :args can be omitted if empty 
    case Token::STEP:
    case Token::STEP_POP:
    {
      bool isPop = (tok==Token::STEP_POP);
      std::string name = d_eparser.parseSymbol();
      Trace("step") << "Check step " << name << std::endl;
      Expr proven;
      // see if we have proven
      tok = d_lex.peekToken();
      if (tok != Token::KEYWORD)
      {
        proven = d_eparser.parseFormula();
      }
      // parse rule name
      std::string keyword = d_eparser.parseKeyword();
      if (keyword!="rule")
      {
        d_lex.parseError("Expected rule in step");
      }
      std::string ruleName = d_eparser.parseSymbol();
      Expr rule = d_eparser.getProofRule(ruleName);
      RuleStat * rs = nullptr;
      if (d_statsEnabled)
      {
        Stats& s = d_state.getStats();
        rs = &s.d_rstats[rule.getValue()];
        RuleStat::start(s);
      }
      // parse premises, optionally
      if (d_lex.peekToken()==Token::KEYWORD)
      {
        keyword = d_eparser.parseKeyword();
      }
      std::vector<Expr> premises;
      if (keyword=="premises")
      {
        std::vector<Expr> given = d_eparser.parseExprList();
        // maybe combine premises
        if (!d_state.getActualPremises(rule.getValue(), given, premises))
        {
          d_lex.parseError("Failed to get premises");
        }
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
      if (d_state.matchesConclusion(rule.getValue()))
      {
        Trace("step") << "Matches conclusion " << ruleName << std::endl;
        if (proven.isNull())
        {
          std::stringstream ss;
          ss << "The proof rule " << ruleName
             << " expects an explicit conclusion.";
          d_lex.parseError(ss.str());
        }
        children.push_back(proven);
      }
      for (const Expr& e : args)
      {
        children.push_back(e);
      }
      // compute the type of applying the rule
      Expr concType;
      if (children.size()>1)
      {
        // check type rule for APPLY directly without constructing the app
        concType = d_eparser.typeCheckApp(children);
      }
      else
      {
        concType = d_eparser.typeCheck(rule);
      }
      // ensure proof type, note this is where "proof checking" happens.
      if (concType.getKind() != Kind::PROOF_TYPE)
      {
        std::stringstream ss;
        ss << "Non-proof conclusion for step, got " << concType;
        d_lex.parseError(ss.str());
      }
      if (!proven.isNull())
      {
        const Expr& actual = concType[0];
        if (actual!=proven)
        {
          std::stringstream ss;
          ss << "Unexpected conclusion for step " << ruleName << ":" << std::endl;
          ss << "    Proves: " << actual << std::endl;
          ss << "  Expected: " << proven;
          d_lex.parseError(ss.str());
        }
      }
      // bind to variable, note that the definition term is not kept
      Expr v = d_state.mkSymbol(Kind::CONST, name, concType);
      d_eparser.bind(name, v);
      // d_eparser.bind(name, def);
      if (isPop)
      {
        d_state.popAssumptionScope();
      }
      if (d_statsEnabled)
      {
        Assert (rs!=nullptr);
        Stats& s = d_state.getStats();
        // increment the stats
        rs->increment(s);
      }
    }
    break;
    //-------------------------- commands to support reading ordinary smt2 inputs
    // (assert <formula>)
    case Token::ASSERT:
    {
      Expr a = d_eparser.parseFormula();
      d_state.addReferenceAssert(a);
    }
    break;
    // (check-sat)
    case Token::CHECK_SAT:
    break;
    // (check-sat-assuming (<formula>*))
    case Token::CHECK_SAT_ASSUMING:
    {
      d_eparser.parseExprList();
    }
    break;
    // (set-logic <logic>)
    case Token::SET_LOGIC:
    {
      d_eparser.parseSymbol();
    }
    break;
    // (set-info <attribute> <sexpr>)
    case Token::SET_INFO:
    {
      std::string key = d_eparser.parseKeyword();
      d_eparser.parseSymbolicExpr();
    }
    break;
    // (set-option <option> <sexpr>)
    case Token::SET_OPTION:
    {
      std::string key = d_eparser.parseKeyword();
      d_eparser.parseSymbolicExpr();
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
