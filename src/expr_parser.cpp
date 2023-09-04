#include "expr_parser.h"

#include <string.h>

#include <iostream>

#include "base/check.h"
#include "base/output.h"
#include "type_checker.h"

namespace alfc {

/**
 * Definition of state identifiers when parsing terms
 *
 * This is required for non-recursive parsing of terms. Note that in SMT-LIB,
 * terms generally are of the form (...anything not involving terms... <term>*)
 * However, let-terms, match-terms, and terms appearing within attributes
 * for term annotations (e.g. quantifier patterns) are exceptions to this.
 * Thus, in the main parsing loop in parseExpr below, we require tracking
 * the context we are in, which dictates how to setup parsing the term after
 * the current one.
 *
 * In each state, the stack contains a topmost ParseOp `op` and a list of
 * arguments `args`, which give a recipe for the term we are parsing. The data
 * in these depend on the context we are in, as documented below.
 */
enum class ParseCtx
{
  /**
   * NEXT_ARG: in context (<op> <term>* <term>
   * `op` specifies the operator we parsed.
   * `args` contain the accumulated list of arguments.
   */
  NEXT_ARG,
  /**
   * Let bindings
   *
   * LET_NEXT_BIND: in context (let (<binding>* (<symbol> <term>
   * `op` contains:
   * - d_name: the name of last bound variable.
   *
   * LET_BODY: in context (let (<binding>*) <term>
   */
  LET_NEXT_BIND,
  LET_BODY,
  /**
   * Match terms
   *
   * MATCH_HEAD: in context (match <term>
   *
   * MATCH_NEXT_CASE: in context (match <term> (<case>* (<pattern> <term>
   * `op` contains:
   * - d_type: set to the type of the head.
   * `args` contain the head term and the accumulated list of case terms.
   */
  MATCH_HEAD,
  MATCH_NEXT_CASE,
  /**
   * Term annotations
   *
   * TERM_ANNOTATE_BODY: in context (! <term>
   */
  TERM_ANNOTATE_BODY
};

ExprParser::ExprParser(Lexer& lex, State& state)
    : d_lex(lex), d_state(state)
{
  d_strToAttr[":var"] = Attr::VAR;
  d_strToAttr[":implicit"] = Attr::IMPLICIT;
  d_strToAttr[":list"] = Attr::LIST;
  d_strToAttr[":syntax"] = Attr::SYNTAX;
  d_strToAttr[":requires"] = Attr::REQUIRES;
  d_strToAttr[":left-assoc"] = Attr::LEFT_ASSOC;
  d_strToAttr[":right-assoc"] = Attr::RIGHT_ASSOC;
  d_strToAttr[":left-assoc-nil"] = Attr::LEFT_ASSOC_NIL;
  d_strToAttr[":right-assoc-nil"] = Attr::RIGHT_ASSOC_NIL;
  d_strToAttr[":chainable"] = Attr::CHAINABLE;
  d_strToAttr[":pairwise"] = Attr::PAIRWISE;
  
  d_strToLiteralKind["<boolean>"] = Kind::BOOLEAN;
  d_strToLiteralKind["<numeral>"] = Kind::NUMERAL;
  d_strToLiteralKind["<decimal>"] = Kind::DECIMAL;
  d_strToLiteralKind["<hexadecimal>"] = Kind::HEXADECIMAL;
  d_strToLiteralKind["<binary>"] = Kind::BINARY;
  d_strToLiteralKind["<string>"] = Kind::STRING;
}

Expr ExprParser::parseExpr()
{
  // the last parsed term
  Expr ret;
  // a request was made to update the current parse context
  bool needsUpdateCtx = false;
  // the last token we read
  Token tok;
  // The stack(s) containing the parse context, the number of scopes, and the
  // arguments for the current expression we are building.
  std::vector<ParseCtx> xstack;
  std::vector<size_t> sstack;
  std::vector<std::vector<Expr>> tstack;
  // Let bindings, dynamically allocated for each let in scope.
  std::vector<std::vector<std::pair<std::string, Expr>>> letBinders;
  do
  {
    Assert(tstack.size() == xstack.size());
    // At this point, we are ready to parse the next term
    tok = d_lex.nextToken();
    Expr currExpr;
    switch (tok)
    {
      // ------------------- open paren
      case Token::LPAREN:
      {
        tok = d_lex.nextToken();
        switch (tok)
        {
          case Token::LET:
          {
            xstack.emplace_back(ParseCtx::LET_NEXT_BIND);
            sstack.emplace_back(0);
            tstack.emplace_back();
            needsUpdateCtx = true;
            letBinders.emplace_back();
          }
          break;
          case Token::MATCH:
          {
            // parse the variable list
            d_state.pushScope();
            std::vector<Expr> vs = parseAndBindSortedVarList();
            std::vector<Expr> args;
            args.emplace_back(d_state.mkExpr(Kind::VARIABLE_LIST, vs));
            xstack.emplace_back(ParseCtx::MATCH_HEAD);
            sstack.emplace_back(1);
            tstack.emplace_back(args);
          }
          break;
          case Token::ATTRIBUTE:
          {
            xstack.emplace_back(ParseCtx::TERM_ANNOTATE_BODY);
            sstack.emplace_back(0);
            tstack.emplace_back();
          }
          break;
          case Token::SYMBOL:
          case Token::QUOTED_SYMBOL:
          {
            // function identifier
            std::string name = tokenStrToSymbol(tok);
            std::vector<Expr> args;
            Expr v = getVar(name);
            args.push_back(v);
            size_t nscopes = 0;
            // if a closure, read a variable list and push a scope
            if (d_state.isClosure(v))
            {
              nscopes = 1;
              // if it is a closure, immediately read the bound variable list
              d_state.pushScope();
              std::vector<Expr> vs = parseAndBindSortedVarList();
              if (vs.empty())
              {
                d_lex.parseError("Expected non-empty sorted variable list");
              }
              Expr vl = d_state.mkExpr(Kind::VARIABLE_LIST, vs);
              args.push_back(vl);
            }
            xstack.emplace_back(ParseCtx::NEXT_ARG);
            sstack.emplace_back(nscopes);
            tstack.emplace_back(args);
          }
          break;
          case Token::UNTERMINATED_QUOTED_SYMBOL:
            d_lex.parseError("Expected SMT-LIBv2 operator", true);
            break;
          default:
            d_lex.unexpectedTokenError(tok, "Expected SMT-LIBv2 operator");
            break;
        }
      }
      break;
      // ------------------- close paren
      case Token::RPAREN:
      {
        // should only be here if we are expecting arguments
        if (tstack.empty() || xstack.back() != ParseCtx::NEXT_ARG)
        {
          d_lex.unexpectedTokenError(
              tok, "Mismatched parentheses in SMT-LIBv2 term");
        }
        // Construct the application term specified by tstack.back()
        ret = d_state.mkExpr(Kind::APPLY, tstack.back());
        //typeCheck(ret);
        // process the scope change
        for (size_t i=0, nscopes = sstack.back(); i<nscopes; i++)
        {
          d_state.popScope();
        }
        // pop the stack
        tstack.pop_back();
        sstack.pop_back();
        xstack.pop_back();
      }
      break;
      // ------------------- base cases
      case Token::SYMBOL:
      case Token::QUOTED_SYMBOL:
      {
        std::string name = tokenStrToSymbol(tok);
        ret = getVar(name);
      }
      break;
      case Token::INTEGER_LITERAL:
      {
        ret = d_state.mkLiteral(Kind::NUMERAL, d_lex.tokenStr());
      }
      break;
      case Token::DECIMAL_LITERAL:
      {
        // must normalize from decimal, since mkLiteral requires a canonical
        // (rational) string input.
        Rational r = Rational::fromDecimal(d_lex.tokenStr());
        ret = d_state.mkLiteral(Kind::DECIMAL, r.toString());
      }
      break;
      case Token::HEX_LITERAL:
      {
        std::string hexStr = d_lex.tokenStr();
        hexStr = hexStr.substr(2);
        ret = d_state.mkLiteral(Kind::HEXADECIMAL, hexStr);
      }
      break;
      case Token::BINARY_LITERAL:
      {
        std::string binStr = d_lex.tokenStr();
        binStr = binStr.substr(2);
        ret = d_state.mkLiteral(Kind::BINARY, binStr);
      }
      break;
      case Token::STRING_LITERAL:
      {
        std::string s = d_lex.tokenStr();
        unescapeString(s);
        // now, must run through String utility so that its unicode
        // handling is unique
        String str(s, true);
        ret = d_state.mkLiteral(Kind::STRING, str.toString());
      }
      break;
      case Token::ABSTRACT_TYPE:
      ret = d_state.mkAbstractType();
      break;
      case Token::TYPE:
      ret = d_state.mkType();
      break;
      case Token::BOOL_TYPE:
      ret = d_state.mkBoolType();
      break;
      case Token::UNTERMINATED_QUOTED_SYMBOL:
        d_lex.parseError("Expected SMT-LIBv2 term", true);
        break;
      default:
        d_lex.unexpectedTokenError(tok, "Expected SMT-LIBv2 term");
        break;
    }

    // Based on the current context, setup next parsed term.
    // We do this only if a context is allocated (!tstack.empty()) and we
    // either just finished parsing a term (!ret.isNull()), or otherwise have
    // indicated that we need to update the context (needsUpdateCtx).
    while (!tstack.empty() && (ret!=nullptr || needsUpdateCtx))
    {
      needsUpdateCtx = false;
      switch (xstack.back())
      {
        // ------------------------- argument lists
        case ParseCtx::NEXT_ARG:
        {
          Assert(ret != nullptr);
          // add it to the list of arguments and clear
          tstack.back().push_back(ret);
          ret = nullptr;
        }
        break;
        // ------------------------- let terms
        case ParseCtx::LET_NEXT_BIND:
        {
          // if we parsed a term, process it as a binding
          if (ret!=nullptr)
          {
            Assert(!letBinders.empty());
            std::vector<std::pair<std::string, Expr>>& bs = letBinders.back();
            // add binding from the symbol to ret
            Assert(!bs.empty());
            bs.back().second = ret;
            ret = nullptr;
            // close the current binding
            d_lex.eatToken(Token::RPAREN);
          }
          else
          {
            // eat the opening left parenthesis of the binding list
            d_lex.eatToken(Token::LPAREN);
          }
          // see if there is another binding
          if (d_lex.eatTokenChoice(Token::LPAREN, Token::RPAREN))
          {
            // (, another binding: setup parsing the next term
            // get the symbol and store in the ParseOp
            std::string name = parseSymbol();
            std::vector<std::pair<std::string, Expr>>& bs = letBinders.back();
            bs.emplace_back(name, Expr());
          }
          else
          {
            // ), we are now looking for the body of the let
            xstack[xstack.size() - 1] = ParseCtx::LET_BODY;
            // push scope
            d_state.pushScope();
            // implement the bindings
            Assert(!letBinders.empty());
            std::vector<std::pair<std::string, Expr>>& bs =
                letBinders.back();
            for (std::pair<std::string, Expr>& b : bs)
            {
              bind(b.first, b.second);
            }
            // done with the binders
            letBinders.pop_back();
          }
        }
        break;
        case ParseCtx::LET_BODY:
        {
          // the let body is the returned term
          d_lex.eatToken(Token::RPAREN);
          xstack.pop_back();
          tstack.pop_back();
          // pop scope
          d_state.popScope();
        }
        break;
        // ------------------------- annotated terms
        case ParseCtx::TERM_ANNOTATE_BODY:
        {
          // now parse attribute list
          AttrMap attrs;
          bool pushedScope = false;
          parseAttributeList(ret, attrs, pushedScope);
          // the scope of the variable is one level up
          if (pushedScope && sstack.size()>1)
          {
            sstack[sstack.size()-2]++;
          }
          // process the attributes
          std::unordered_set<Attr> rmAttr;
          for (std::pair<const Attr, std::vector<Expr>>& a : attrs)
          {
            switch(a.first)
            {
              case Attr::VAR:
              {
                Assert (a.second.size()==1);
                // it is now (Quote v) for that variable
                ret = d_state.mkQuoteType(a.second[0]);
                rmAttr.insert(a.first);
              }
                break;
              case Attr::IMPLICIT:
                // the term will not be added as an argument to the parent
                ret = nullptr;
                rmAttr.insert(a.first);
                break;
              case Attr::REQUIRES:
                ret = d_state.mkRequires(a.second, ret);
                rmAttr.insert(a.first);
                break;
              default:
                break;
            }
          }
          // remove the attributes processed above
          for (Attr a : rmAttr)
          {
            attrs.erase(a);
          }
          // mark the remaining attributes
          if (!attrs.empty())
          {
            if (ret!=nullptr)
            {
              d_state.markAttributes(ret, attrs);
            }
            // TODO: else warn about unprocessed attributes?
          }
          d_lex.eatToken(Token::RPAREN);
          // finished parsing attributes, ret is either nullptr if implicit,
          // or the term we parsed as the body of the annotation.
          // process the scope change
          for (size_t i=0, nscopes = sstack.back(); i<nscopes; i++)
          {
            d_state.popScope();
          }
          xstack.pop_back();
          sstack.pop_back();
          tstack.pop_back();
        }
        break;
        // ------------------------- match terms
        case ParseCtx::MATCH_HEAD:
        {
          Assert(ret!=nullptr);
          // add the head
          tstack.back().push_back(ret);
          ret = nullptr;
          // we now parse a pattern
          xstack[xstack.size() - 1] = ParseCtx::MATCH_NEXT_CASE;
          needsUpdateCtx = true;
        }
        break;
        case ParseCtx::MATCH_NEXT_CASE:
        {
          std::vector<Expr>& args = tstack.back();
          bool checkNextPat = true;
          if (ret!=nullptr)
          {
            // if we just got done parsing a term (either a pattern or a return)
            Expr last = args.back();
            if (args.size()>2 && last->getKind()!=Kind::PAIR)
            {
              // case where we just read a return value
              // replace the back of this with a pair
              args.back() = d_state.mkPair(last, ret);
              d_lex.eatToken(Token::RPAREN);
            }
            else
            {
              // case where we just read a pattern
              args.push_back(ret);
              checkNextPat = false;
            }
            ret = nullptr;
          }
          // if no more cases, we are done
          if (checkNextPat)
          {
            if (d_lex.eatTokenChoice(Token::RPAREN, Token::LPAREN))
            {
              Trace("parser") << "Parsed match " << args << std::endl;
              // make a program
              if (args.size()<=2)
              {
                d_lex.parseError("Expected non-empty list of cases");
              }
              Expr atype = d_state.mkAbstractType();
              // environment is the variable list
              const std::vector<Expr>& vl = args[0]->getChildren();
              Expr hd = args[1];
              std::vector<Expr> allVars = ExprValue::getVariables(args);
              std::vector<Expr> env;
              std::vector<Expr> fargTypes;
              fargTypes.push_back(atype);
              for (const Expr& v : allVars)
              {
                if (std::find(vl.begin(), vl.end(), v)==vl.end())
                {
                  // A variable not appearing in the local binding of the match,
                  // add it to the environment.
                  env.push_back(v);
                  // It will be an argument to the internal program
                  fargTypes.push_back(atype);
                }
              }
              Trace("parser") << "Binder is " << vl << std::endl;
              Trace("parser") << "Env is " << env << std::endl;
              // make the program variable, whose type is abstract
              Expr ftype = d_state.mkFunctionType(fargTypes, atype);
              std::stringstream pvname;
              pvname << "_match_" << hd;
              Expr pv = d_state.mkProgramConst(pvname.str(), ftype);
              // process the cases
              std::vector<Expr> cases;
              for (size_t i=2, nargs = args.size(); i<nargs; i++)
              {
                Expr cs = args[i];
                Assert (cs->getKind()==Kind::PAIR);
                Expr lhs = (*cs.get())[0];
                // check that variables in the pattern are only from the binder
                ensureBound(lhs, vl);
                Expr rhs = (*cs.get())[1];
                std::vector<Expr> appArgs{pv, lhs};
                appArgs.insert(appArgs.end(), env.begin(), env.end());
                Expr lhsa = d_state.mkExpr(Kind::APPLY, appArgs);
                cases.push_back(d_state.mkPair(lhsa, rhs));
              }
              Expr prog = d_state.mkExpr(Kind::PROGRAM, cases);
              d_state.defineProgram(pv, prog);
              std::vector<Expr> appArgs{pv, hd};
              appArgs.insert(appArgs.end(), env.begin(), env.end());
              ret = d_state.mkExpr(Kind::APPLY, appArgs);
              // HACK pop one scope
              d_state.popScope();
              xstack.pop_back();
              sstack.pop_back();
              tstack.pop_back();
            }
          }
          // otherwise, ready to parse the next expression
        }
        break;
        default: break;
      }
    }
    // otherwise ret will be returned
  } while (!tstack.empty());
  return ret;
}

Expr ExprParser::parseType()
{
  Expr e = parseExpr();
  // ensure it is a type
  typeCheck(e, d_state.mkType());
  return e;
}

Expr ExprParser::parseFormula()
{
  Expr e = parseExpr();
  // ensure it has type Bool
  typeCheck(e, d_state.mkBoolType());
  return e;
  
}

std::vector<Expr> ExprParser::parseExprList()
{
  d_lex.eatToken(Token::LPAREN);
  std::vector<Expr> terms;
  Token tok = d_lex.nextToken();
  while (tok != Token::RPAREN)
  {
    d_lex.reinsertToken(tok);
    Expr t = parseExpr();
    terms.push_back(t);
    tok = d_lex.nextToken();
  }
  return terms;
}

std::vector<Expr> ExprParser::parseTypeList()
{
  d_lex.eatToken(Token::LPAREN);
  std::vector<Expr> terms;
  Token tok = d_lex.nextToken();
  while (tok != Token::RPAREN)
  {
    d_lex.reinsertToken(tok);
    Expr t = parseType();
    terms.push_back(t);
    tok = d_lex.nextToken();
  }
  return terms;
}

Expr ExprParser::parseExprPair()
{
  d_lex.eatToken(Token::LPAREN);
  Expr t1 = parseExpr();
  Expr t2 = parseExpr();
  d_lex.eatToken(Token::RPAREN);
  return d_state.mkExpr(Kind::PAIR, {t1, t2});
}

std::vector<Expr> ExprParser::parseExprPairList()
{
  d_lex.eatToken(Token::LPAREN);
  std::vector<Expr> terms;
  while (d_lex.eatTokenChoice(Token::LPAREN, Token::RPAREN))
  {
    Expr t1 = parseExpr();
    Expr t2 = parseExpr();
    Expr t = d_state.mkPair(t1, t2);
    terms.push_back(t);
    d_lex.eatToken(Token::RPAREN);
  }
  return terms;
}

std::vector<Expr> ExprParser::parseAndBindSortedVarList()
{
  std::vector<Expr> varList;
  d_lex.eatToken(Token::LPAREN);
  std::string name;
  Expr t;
  // while the next token is LPAREN, exit if RPAREN
  while (d_lex.eatTokenChoice(Token::LPAREN, Token::RPAREN))
  {
    name = parseSymbol();
    t = parseType();
    Expr v = d_state.mkParameter(name, t);
    bind(name, v);
    // parse attribute list
    AttrMap attrs;
    parseAttributeList(v, attrs);
    d_state.markAttributes(v, attrs);
    d_lex.eatToken(Token::RPAREN);
    varList.push_back(v);
  }
  return varList;
}

std::string ExprParser::parseSymbol()
{
  Token tok = d_lex.nextToken();
  return tokenStrToSymbol(tok);
}

std::vector<std::string> ExprParser::parseSymbolList()
{
  d_lex.eatToken(Token::LPAREN);
  std::vector<std::string> symbols;
  Token tok = d_lex.nextToken();
  while (tok != Token::RPAREN)
  {
    d_lex.reinsertToken(tok);
    std::string sym = parseSymbol();
    symbols.push_back(sym);
    tok = d_lex.nextToken();
  }
  return symbols;
}

bool ExprParser::parseDatatypesDef(
      const std::vector<std::string>& dnames,
      const std::vector<size_t>& arities,
      std::map<Expr, std::vector<Expr>>& dts,
      std::map<Expr, std::vector<Expr>>& dtcons)
{
  Assert(dnames.size() == arities.size()
         || (dnames.size() == 1 && arities.empty()));
  // Declare the datatypes that are currently being defined as unresolved
  // types. If we do not know the arity of the datatype yet, we wait to
  // define it until parsing the preamble of its body, which may optionally
  // involve `par`. This is limited to the case of single datatypes defined
  // via declare-datatype, and hence no datatype body is parsed without
  // having all types declared. This ensures we can parse datatypes with
  // nested recursion, e.g. datatypes D having a subfield type
  // (Array Int D).
  std::vector<Expr> dtlist;
  for (unsigned i = 0, dsize = dnames.size(); i < dsize; i++)
  {
    if (i >= arities.size())
    {
      // do not know the arity yet
      continue;
    }
    // make the datatype, which has the given arity
    Expr t = d_state.mkTypeConstant(dnames[i], arities[i]);
    // bind
    if (!d_state.bind(dnames[i], t))
    {
      return false;
    }
    dtlist.push_back(t);
  }
  // while we get another datatype declaration, or close the list
  Token tok = d_lex.nextToken();
  size_t i = 0;
  while (tok == Token::LPAREN)
  {
    std::vector<Expr> params;
    if (i >= dnames.size())
    {
      d_lex.parseError("Too many datatypes defined in this block.");
    }
    tok = d_lex.nextToken();
    bool pushedScope = false;
    if (tok == Token::PAR)
    {
      pushedScope = true;
      d_state.pushScope();
      std::vector<std::string> symList = parseSymbolList();
      if (symList.empty())
      {
        d_lex.parseError("Expected non-empty parameter list");
      }
      // parameters are type variables
      for (const std::string& sym : symList)
      {
        Expr t = d_state.mkParameter(sym, d_state.mkType());
        if (!d_state.bind(sym, t))
        {
          return false;
        }
        params.push_back(t);
      }
    }
    else
    {
      d_lex.reinsertToken(tok);
      // we will parse the parentheses-enclosed construct list below
      d_lex.reinsertToken(Token::LPAREN);
    }
    if (i >= arities.size())
    {
      // if the arity is not yet fixed, bind it now
      Expr t = d_state.mkTypeConstant(dnames[i], params.size());
      // bind
      if (!d_state.bind(dnames[i], t))
      {
        return false;
      }
      dtlist.push_back(t);
    }
    else if (arities[i] >= 0 && params.size() != arities[i])
    {
      // if the arity was fixed by prelude and is not equal to the number of
      // parameters
      d_lex.parseError("Wrong number of parameters for datatype.");
    }
    // read constructor definition list, populate into the current datatype
    Expr& dt = dtlist[i];
    Expr dti = dt;
    if (!params.empty())
    {
      std::vector<Expr> dapp;
      dapp.push_back(dt);
      dapp.insert(dapp.end(), params.begin(), params.end());
      dti = d_state.mkExpr(Kind::APPLY, dapp);
    }
    std::vector<std::pair<std::string, Expr>> toBind;
    parseConstructorDefinitionList(dti, dts[dt], dtcons, toBind);
    if (pushedScope)
    {
      d_lex.eatToken(Token::RPAREN);
      d_state.popScope();
    }
    for (std::pair<std::string, Expr>& b : toBind)
    {
      if (!d_state.bind(b.first, b.second))
      {
        return false;
      }
    }
    tok = d_lex.nextToken();
    i++;
  }
  if (dtlist.size() != dnames.size())
  {
    d_lex.unexpectedTokenError(tok, "Wrong number of datatypes provided.");
  }
  d_lex.reinsertToken(tok);
  return true;
}

void ExprParser::parseConstructorDefinitionList(Expr& dt,
                                                std::vector<Expr>& conslist,
                                                std::map<Expr, std::vector<Expr>>& dtcons,
                                                std::vector<std::pair<std::string, Expr>>& toBind)
{
  d_lex.eatToken(Token::LPAREN);
  Expr boolType = d_state.mkBoolType();
  // parse another constructor or close the list
  while (d_lex.eatTokenChoice(Token::LPAREN, Token::RPAREN))
  {
    std::string name = parseSymbol();
    std::vector<Expr> typelist;
    std::vector<Expr> sels;
    // parse another selector or close the current constructor
    while (d_lex.eatTokenChoice(Token::LPAREN, Token::RPAREN))
    {
      std::string id = parseSymbol();
      Expr t = parseType();
      typelist.push_back(t);
      Expr stype = d_state.mkFunctionType({dt}, t);
      Expr sel = d_state.mkConst(id, stype);
      toBind.emplace_back(id,sel);
      sels.push_back(sel);
      std::stringstream ss;
      ss << "update-" << id;
      Expr utype = d_state.mkFunctionType({dt, t}, dt);
      Expr updater = d_state.mkConst(ss.str(), utype);
      toBind.emplace_back(ss.str(), updater);
      d_lex.eatToken(Token::RPAREN);
    }
    Expr ctype = d_state.mkFunctionType(typelist, dt);
    Expr cons = d_state.mkConst(name, ctype);
    toBind.emplace_back(name, cons);
    conslist.push_back(cons);
    // make the discriminator
    std::stringstream ss;
    ss << "is-" << name;
    Expr dtype = d_state.mkFunctionType({dt}, boolType);
    Expr tester = d_state.mkConst(ss.str(), dtype);
    toBind.emplace_back(ss.str(), tester);
    dtcons[cons] = sels;
  }
}

std::string ExprParser::parseKeyword()
{
  d_lex.eatToken(Token::KEYWORD);
  std::string s = d_lex.tokenStr();
  // strip off the initial colon
  return s.erase(0, 1);
}

uint32_t ExprParser::parseIntegerNumeral()
{
  d_lex.eatToken(Token::INTEGER_LITERAL);
  return tokenStrToUnsigned();
}

uint32_t ExprParser::tokenStrToUnsigned()
{
  // forbid leading zeroes?
  std::string token = d_lex.tokenStr();
  if (token.size() > 1 && token[0] == '0')
  {
    d_lex.parseError("Numeral with leading zeroes are forbidden");
  }
  uint32_t result;
  std::stringstream ss;
  ss << d_lex.tokenStr();
  ss >> result;
  return result;
}

std::string ExprParser::tokenStrToSymbol(Token tok)
{
  std::string id;
  switch (tok)
  {
    case Token::SYMBOL: id = d_lex.tokenStr(); break;
    case Token::QUOTED_SYMBOL:
      id = d_lex.tokenStr();
      // strip off the quotes
      id = id.erase(0, 1);
      id = id.erase(id.size() - 1, 1);
      break;
    case Token::UNTERMINATED_QUOTED_SYMBOL:
      d_lex.parseError("Expected SMT-LIBv2 symbol", true);
      break;
    default:
      d_lex.unexpectedTokenError(tok, "Expected SMT-LIBv2 symbol");
      break;
  }
  return id;
}

std::string ExprParser::parseStr(bool unescape)
{
  d_lex.eatToken(Token::STRING_LITERAL);
  std::string s = d_lex.tokenStr();
  if (unescape)
  {
    unescapeString(s);
  }
  return s;
}

void ExprParser::parseAttributeList(const Expr& e, AttrMap& attrs, bool& pushedScope)
{
  std::map<std::string, Attr>::iterator its;
  // while the next token is KEYWORD, exit if RPAREN
  while (d_lex.eatTokenChoice(Token::KEYWORD, Token::RPAREN))
  {
    std::string key = d_lex.tokenStr();
    its = d_strToAttr.find(key);
    Expr val;
    if (its==d_strToAttr.end())
    {
      // TODO: parse and skip value?
      // store dummy, to mark that we read an attribute
      Warning() << "Unsupported attribute " << key;
      attrs[Attr::NONE].push_back(val);
      continue;
    }
    switch (its->second)
    {
      case Attr::VAR:
      {
        if (attrs.find(Attr::VAR)!=attrs.end())
        {
          d_lex.parseError("Cannot use :var on the same term more than once");
        }
        std::string name = parseSymbol();
        // e should be a type
        val = d_state.mkParameter(name, e);
        // immediately bind
        if (!pushedScope)
        {
          pushedScope = true;
          d_state.pushScope();
        }
        bind(name, val);
      }
        break;
      case Attr::LIST:
      case Attr::IMPLICIT:
      case Attr::RIGHT_ASSOC_NIL:
      case Attr::LEFT_ASSOC_NIL:
        // requires no value
        break;
      case Attr::RIGHT_ASSOC:
      case Attr::LEFT_ASSOC:
      {
        // optional value
        Token tok = d_lex.peekToken();
        if (tok!=Token::RPAREN && tok!=Token::KEYWORD)
        {
          val = parseExpr();
        }
      } 
        break;
      case Attr::CHAINABLE:
      case Attr::PAIRWISE:
      {
        // requires an expression that follows
        val = parseExpr();
      }
        break;
      case Attr::REQUIRES:
      {
        // requires a pair
        val = parseExprPair();
      }
        break;
      default:
        d_lex.parseError("Unhandled attribute");
        break;
    }
    attrs[its->second].push_back(val);
  }
  d_lex.reinsertToken(Token::RPAREN);
}

void ExprParser::parseAttributeList(const Expr& e, AttrMap& attrs)
{
  bool pushedScope = false;
  parseAttributeList(e, attrs, pushedScope);
  // pop the scope if necessary
  if (pushedScope)
  {
    d_state.popScope();
  }
}

Kind ExprParser::parseLiteralKind()
{
  std::string name = parseSymbol();
  std::map<std::string, Kind>::iterator it = d_strToLiteralKind.find(name);
  if (it==d_strToLiteralKind.end())
  {
    std::stringstream ss;
    ss << "Unknown literal kind " << name;
    d_lex.parseError(ss.str());
  }
  return it->second;
}

void ExprParser::unescapeString(std::string& s)
{
  // strip off the quotes
  s = s.erase(0, 1);
  s = s.erase(s.size() - 1, 1);
  for (size_t i = 0, ssize = s.size(); i < ssize; i++)
  {
    if ((unsigned)s[i] > 127 && !isprint(s[i]))
    {
      d_lex.parseError(
          "Extended/unprintable characters are not "
          "part of SMT-LIB, and they must be encoded "
          "as escape sequences");
    }
  }
  size_t dst = 0;
  for (size_t src = 0; src<s.size(); ++src, ++dst)
  {
    s[dst] = s[src];
    if (s[src]=='"')
    {
      ++src;
    }
  }
  s.erase(dst);
}

Expr ExprParser::getVar(const std::string& name)
{
  Expr ret = d_state.getVar(name);
  if (ret==nullptr)
  {
    std::stringstream ss;
    ss << "Could not find symbol " << name;
    d_lex.parseError(ss.str());
  }
  return ret;
}

Expr ExprParser::getProofRule(const std::string& name)
{
  Expr v = getVar(name);
  if (v->getKind()!=Kind::PROOF_RULE)
  {
    std::stringstream ss;
    ss << "Expected proof rule for " << name;
    d_lex.parseError(ss.str());
  }
  return v;
}

void ExprParser::bind(const std::string& name, Expr& e)
{
  if (!d_state.bind(name, e))
  {
    std::stringstream ss;
    ss << "Failed to bind symbol " << name;
    d_lex.parseError(ss.str());
  }
}

Expr ExprParser::typeCheck(Expr& e)
{
  // type check immediately
  const Expr& v = d_state.getTypeChecker().getType(e);
  if (v==nullptr)
  {
    // we allocate stringstream for error messages only when an error occurs
    // thus, we require recomputing the error message here.
    std::stringstream ss;
    d_state.getTypeChecker().getType(e, &ss);
    std::stringstream msg;
    msg << "Type checking failed:" << std::endl;
    msg << "Expression: " << e << std::endl;
    msg << "Message: " << ss.str() << std::endl;
    d_lex.parseError(msg.str());
  }
  return v;
}
Expr ExprParser::typeCheckApp(std::vector<Expr>& children)
{
  // ensure all children are type checked
  for (Expr& c : children)
  {
    typeCheck(c);
  }
  const Expr& v = d_state.getTypeChecker().getTypeApp(children);
  if (v==nullptr)
  {
    // we allocate stringstream for error messages only when an error occurs
    // thus, we require recomputing the error message here.
    std::stringstream ss;
    d_state.getTypeChecker().getTypeApp(children, &ss);
    std::stringstream msg;
    msg << "Type checking application failed:" << std::endl;
    msg << "Children: " << children << std::endl;
    msg << "Message: " << ss.str() << std::endl;
    d_lex.parseError(msg.str());
  }
  return v;
}

Expr ExprParser::typeCheck(Expr& e, const Expr& expected)
{
  Expr et = typeCheck(e);
  if (et!=expected)
  {
    std::stringstream msg;
    msg << "Expression of unexpected type:" << std::endl;
    msg << "Expression: " << e << std::endl;
    msg << "      Type: " << et << std::endl;
    msg << "  Expected: " << expected << std::endl;
    d_lex.parseError(msg.str());
  }
  return et;
}

void ExprParser::ensureBound(Expr& e, const std::vector<Expr>& bvs)
{
  std::vector<Expr> efv = ExprValue::getVariables(e);
  for (const Expr& v : efv)
  {
    if (std::find(bvs.begin(), bvs.end(), v)==bvs.end())
    {
      std::stringstream msg;
      msg << "Unexpected free variable in expression:" << std::endl;
      msg << "     Expression: " << e << std::endl;
      msg << "  Free variable: " << v << std::endl;
      msg << "Bound variables: " << bvs << std::endl;
      d_lex.parseError(msg.str());
    }
  }
}

}  // namespace alfc
