#include "expr_parser.h"

#include <string.h>

namespace atc {

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
   * Term annotations
   *
   * TERM_ANNOTATE_BODY: in context (! <term>
   *
   * TERM_ANNOTATE_NEXT_ATTR: in context (! <term> <attr>* <keyword> <term_spec>
   * where notice that <term_spec> may be a term or a list of terms.
   * `op` contains:
   * - d_expr: the body of the term annotation.
   * - d_kind: the kind to apply to the current <term_spec> (if any).
   * `args` contain the accumulated patterns or quantifier attributes.
   */
  TERM_ANNOTATE_BODY,
  TERM_ANNOTATE_NEXT_ATTR
};

ExprParser::ExprParser(Lexer& lex, State& state)
    : d_lex(lex), d_state(state)
{
}

Expr ExprParser::parseExpr()
{
  // the last parsed term
  Expr ret;
  // a request was made to update the current parse context
  bool needsUpdateCtx = false;
  // the last token we read
  Token tok;
  // The stack(s) containing the parse context, and the recipe for the
  // current we are building.
  std::vector<ParseCtx> xstack;
  std::vector<size_t> sstack;
  std::vector<std::vector<Expr>> tstack;
  // Let bindings, dynamically allocated for each let in scope.
  std::vector<std::vector<std::pair<std::string, Expr>>> letBinders;
  do
  {
    //Assert(tstack.size() == xstack.size());
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
              std::vector<std::pair<std::string, Expr>> sortedVarNames =
                  parseSortedVarList();
              if (sortedVarNames.empty())
              {
                d_lex.parseError("Expected non-empty sorted variable list");
              }
              std::vector<Expr> vs;
              if (!d_state.mkAndBindVars(sortedVarNames, vs))
              {
                d_lex.parseError("Failed to bind sorted variable list");
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
        typeCheck(ret);
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
        ret = d_state.mkLiteral(Kind::INTEGER, d_lex.tokenStr());
      }
      break;
      case Token::DECIMAL_LITERAL:
      {
        ret = d_state.mkLiteral(Kind::DECIMAL, d_lex.tokenStr());
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
        ret = d_state.mkLiteral(Kind::STRING, s);
      }
      break;
      case Token::ABSTRACT_TYPE:
      ret = d_state.mkAbstractType();
      break;
      case Token::TYPE:
      ret = d_state.mkType();
      break;
      case Token::PROOF_TYPE:
      ret = d_state.mkProofType();
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
          //Assert(!ret.isNull());
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
            //Assert(!letBinders.empty());
            std::vector<std::pair<std::string, Expr>>& bs = letBinders.back();
            // add binding from the symbol to ret
            //Assert (!bs.empty());
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
            //Assert(!letBinders.empty());
            const std::vector<std::pair<std::string, Expr>>& bs =
                letBinders.back();
            for (const std::pair<std::string, Expr>& b : bs)
            {
              if (!d_state.bind(b.first, b.second))
              {
                // TODO: error
              }
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
          // save ret as the expression and clear
          tstack.back().push_back(ret);
          ret = nullptr;
          // now parse attribute list
          xstack[xstack.size() - 1] = ParseCtx::TERM_ANNOTATE_NEXT_ATTR;
          needsUpdateCtx = true;
          // ensure there is at least one attribute
          tok = d_lex.peekToken();
          if (tok == Token::RPAREN)
          {
            d_lex.parseError(
                "Expecting at least one attribute for term annotation.");
          }
        }
        break;
        case ParseCtx::TERM_ANNOTATE_NEXT_ATTR:
        {
          // see if there is another keyword
          if (d_lex.eatTokenChoice(Token::KEYWORD, Token::RPAREN))
          {
            std::string key = d_lex.tokenStr();
            // Based on the keyword, determine the context.
            if (key == ":var")
            {
              std::string name = parseSymbol();
              needsUpdateCtx = true;
              // bind the current, add a scope
              d_state.pushScope();
              Expr v = d_state.mkVar(name, tstack.back()[0]);
              if (!d_state.bind(name, v))
              {
              }
              sstack.back() = sstack.back()+1;
            }
            else if (key == ":implicit")
            {
              needsUpdateCtx = true;
            }
            else
            {
              // warn that the attribute is not supported
              std::stringstream ss;
              ss << "Annotation " << d_lex.tokenStr() << " not supported.";
              d_lex.warning(ss.str());
              tok = d_lex.nextToken();
              // We don't know whether to expect an attribute value. Thus,
              // we will either see keyword (the next attribute), rparen
              // (the term annotation is finished), or else parse as generic
              // symbolic expression for the current attribute.
              switch (tok)
              {
                case Token::KEYWORD:
                case Token::RPAREN:
                  // finished with this attribute, go to the next one if it
                  // exists.
                  d_lex.reinsertToken(tok);
                  needsUpdateCtx = true;
                  break;
                default:
                  // TODO: ignore the symbolic expression that follows
                  d_lex.reinsertToken(tok);
                  // will parse another attribute
                  break;
              }
            }
          }
          // if we instead saw a RPAREN_TOK, we are finished
          else
          {
            //Assert(!tstack.back().size()==1);
            // finished parsing attributes, we will return the original term
            ret = tstack.back()[0];
            xstack.pop_back();
            sstack.pop_back();
            tstack.pop_back();
          }
        }
        break;
        default: break;
      }
    }
    // otherwise ret will be returned
  } while (!tstack.empty());
  return ret;
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

std::vector<std::pair<std::string, Expr>> ExprParser::parseSortedVarList()
{
  std::vector<std::pair<std::string, Expr>> varList;
  d_lex.eatToken(Token::LPAREN);
  std::string name;
  Expr t;
  // while the next token is LPAREN, exit if RPAREN
  while (d_lex.eatTokenChoice(Token::LPAREN, Token::RPAREN))
  {
    name = parseSymbol();
    t = parseExpr();
    varList.emplace_back(name, t);
    d_lex.eatToken(Token::RPAREN);
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

std::vector<std::string> ExprParser::parseNumeralList()
{
  std::vector<std::string> numerals;
  Token tok = d_lex.nextToken();
  while (tok == Token::INTEGER_LITERAL)
  {
    numerals.emplace_back(d_lex.tokenStr());
    tok = d_lex.nextToken();
  }
  d_lex.reinsertToken(tok);
  return numerals;
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
    ss << "State::getVar: could not find symbol " << name;
    d_lex.parseError(ss.str());
  }
  return ret;
}

void ExprParser::typeCheck(const Expr& e)
{
  // type check immediately
  std::stringstream ss;
  if (e->getType(ss)==nullptr)
  {
    std::stringstream msg;
    msg << "Type checking failed: " << ss.str();
    d_lex.parseError(msg.str());
  }
}

}  // namespace atc
