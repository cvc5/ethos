/******************************************************************************
 * This file is part of the alfc project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#include "lexer.h"

#include <cassert>
#include <iostream>
#include <sstream>

#include "base/check.h"

namespace alfc {

std::ostream& operator<<(std::ostream& o, const Location& l)
{
  return o << l.d_line << ":" << l.d_column;
}
std::ostream& operator<<(std::ostream& o, const Span& l)
{
  return o << l.d_start << "-" << l.d_end;
}

Lexer::Lexer(bool lexLet)
    : d_lexLet(lexLet), d_isInteractive(false), d_bufferPos(0), d_bufferEnd(0),
      d_peekedChar(false), d_chPeeked(0)
{
  for (int32_t ch = 'a'; ch <= 'z'; ++ch)
  {
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::SYMBOL_START);
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::SYMBOL);
  }
  for (int32_t ch = 'a'; ch <= 'f'; ++ch)
  {
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::HEXADECIMAL_DIGIT);
  }
  for (int32_t ch = 'A'; ch <= 'Z'; ++ch)
  {
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::SYMBOL_START);
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::SYMBOL);
  }
  for (int32_t ch = 'A'; ch <= 'F'; ++ch)
  {
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::HEXADECIMAL_DIGIT);
  }
  for (int32_t ch = '0'; ch <= '9'; ++ch)
  {
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::HEXADECIMAL_DIGIT);
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::DECIMAL_DIGIT);
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::SYMBOL);
  }
  d_charClass['0'] |= static_cast<uint32_t>(CharacterClass::BIT);
  d_charClass['1'] |= static_cast<uint32_t>(CharacterClass::BIT);
  // ~!@$%^&*_-+|=<>.?/
  for (int32_t ch : s_extraSymbolChars)
  {
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::SYMBOL_START);
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::SYMBOL);
  }
  // whitespace
  d_charClass[' '] |= static_cast<uint32_t>(CharacterClass::WHITESPACE);
  d_charClass['\t'] |= static_cast<uint32_t>(CharacterClass::WHITESPACE);
  d_charClass['\r'] |= static_cast<uint32_t>(CharacterClass::WHITESPACE);
  d_charClass['\n'] |= static_cast<uint32_t>(CharacterClass::WHITESPACE);
}

void Lexer::warning(const std::string& msg)
{
  std::cout << d_inputName << ':' << d_span.d_start.d_line << '.'
            << d_span.d_start.d_column << ": " << msg << std::endl;
}

void Lexer::parseError(const std::string& msg, bool eofException)
{
  std::stringstream os;
  if( d_span.d_start.d_line > 0 ) {
    ALFC_FATAL() << "Error: " << d_inputName << ":"
                 << d_span.d_start.d_line << "." << d_span.d_start.d_column
                 << ": " << msg << std::endl;
  } else {
    ALFC_FATAL() << "Error: " << msg << std::endl;
  }
}

void Lexer::initSpan()
{
  d_span.d_start.d_line = 1;
  d_span.d_start.d_column = 0;
  d_span.d_end.d_line = 1;
  d_span.d_end.d_column = 0;
}

void Lexer::initialize(Input* input, const std::string& inputName)
{
  Assert(input != nullptr);
  d_istream = input->getStream();
  d_isInteractive = input->isInteractive();
  d_inputName = inputName;
  initSpan();
  d_peeked.clear();
  d_bufferPos = 0;
  d_bufferEnd = 0;
  d_peekedChar = false;
  d_chPeeked = 0;
}

Token Lexer::nextToken()
{
  if (d_peeked.empty())
  {
    return nextTokenInternal();
  }
  Token t = d_peeked.back();
  d_peeked.pop_back();
  return t;
}

Token Lexer::peekToken()
{
  // since d_peeked is first in, last out, we should not peek more than once
  // or the order is swapped.
  Assert(d_peeked.empty());
  // parse next token
  Token t = nextTokenInternal();
  // reinsert it immediately
  reinsertToken(t);
  // return it
  return t;
}

void Lexer::reinsertToken(Token t) { d_peeked.push_back(t); }

void Lexer::unexpectedTokenError(Token t, const std::string& info)
{
  Assert(d_peeked.empty());
  std::ostringstream o{};
  o << info << ", got `" << tokenStr() << "` (" << t << ")." << std::endl;
  // Note that we treat this as an EOF exception if the token is EOF.
  // This is important for exception handling in interactive mode.
  parseError(o.str(), t == Token::EOF_TOK);
}

void Lexer::eatToken(Token t)
{
  Token tt = nextToken();
  if (t != tt)
  {
    std::ostringstream o{};
    o << "Expected a " << t;
    unexpectedTokenError(tt, o.str());
  }
}

bool Lexer::eatTokenChoice(Token t, Token f)
{
  Token tt = nextToken();
  if (tt == t)
  {
    return true;
  }
  else if (tt != f)
  {
    std::ostringstream o{};
    o << "Expected " << t << " or " << f;
    unexpectedTokenError(tt, o.str());
  }
  return false;
}


const char* Lexer::tokenStr() const
{
  Assert(!d_token.empty() && d_token.back() == 0);
  return d_token.data();
}

Token Lexer::nextTokenInternal()
{
  //Trace("lexer-debug") << "Call nextToken" << std::endl;
  d_token.clear();
  Token ret = computeNextToken();
  // null terminate?
  d_token.push_back(0);
  //Trace("lexer-debug") << "Return nextToken " << ret << " / " << tokenStr() << std::endl;
  return ret;
}

Token Lexer::computeNextToken()
{
  bumpSpan();
  int32_t ch;
  // skip whitespace and comments
  for (;;)
  {
    do
    {
      if ((ch = nextChar()) == EOF)
      {
        return Token::EOF_TOK;
      }
    } while (isCharacterClass(ch, CharacterClass::WHITESPACE));

    if (ch != ';')
    {
      break;
    }
    while ((ch = nextChar()) != '\n')
    {
      if (ch == EOF)
      {
        return Token::EOF_TOK;
      }
    }
  }
  bumpSpan();
  pushToToken(ch);
  switch (ch)
  {
    case '!': return Token::ATTRIBUTE;
    case '(': return Token::LPAREN;
    case ')': return Token::RPAREN;
    case '|':
      do
      {
        ch = nextChar();
        if (ch == EOF)
        {
          return Token::UNTERMINATED_QUOTED_SYMBOL;
        }
        pushToToken(ch);
      } while (ch != '|');
      return Token::QUOTED_SYMBOL;
    case '#':
      ch = nextChar();
      switch (ch)
      {
        case 'b':
          pushToToken(ch);
          // parse [01]*
          parseCharList(CharacterClass::BIT);
          return Token::BINARY_LITERAL;
        case 'x':
          pushToToken(ch);
          // parse [0-9a-fA-F]*
          parseCharList(CharacterClass::HEXADECIMAL_DIGIT);
          return Token::HEX_LITERAL;
        default:
          // otherwise error
          parseError("Error finding token following #");
          break;
      }
      break;
    case '"':
      for (;;)
      {
        ch = nextChar();
        if (ch == EOF)
        {
          return Token::UNTERMINATED_STRING_LITERAL;
        }
        else if (ch == '"')
        {
          pushToToken(ch);
          ch = nextChar();
          // "" denotes the escape sequence for "
          if (ch != '"')
          {
            saveChar(ch);
            return Token::STRING_LITERAL;
          }
        }
        pushToToken(ch);
      }
      break;
    case ':':
      // parse a simple symbol
      if (!parseChar(CharacterClass::SYMBOL_START))
      {
        parseError("Error expected symbol following :");
      }
      parseNonEmptyCharList(CharacterClass::SYMBOL);
      return Token::KEYWORD;
    default:
      if (isCharacterClass(ch, CharacterClass::DECIMAL_DIGIT))
      {
        Token res = Token::INTEGER_LITERAL;
        // parse [0-9]*
        parseCharList(CharacterClass::DECIMAL_DIGIT);
        // maybe .[0-9]+
        ch = nextChar();
        if (ch == '.' || ch=='/')
        {
          pushToToken(ch);
          res = ch == '.' ? Token::DECIMAL_LITERAL : Token::RATIONAL_LITERAL;
          // parse [0-9]+
          if (!parseNonEmptyCharList(CharacterClass::DECIMAL_DIGIT))
          {
            parseError("Error expected decimal string following .");
          }
        }
        else
        {
          // otherwise, undo
          saveChar(ch);
        }
        return res;
      }
      else if (isCharacterClass(ch, CharacterClass::SYMBOL_START))
      {
        // otherwise, we are a simple symbol or standard alphanumeric token
        // note that we group the case when `:` is here.
        parseCharList(CharacterClass::SYMBOL);
        // tokenize the current symbol, which may be a special case
        return tokenizeCurrentSymbol();
      }
      // otherwise error
      break;
  }
  parseError("Error finding token");
  return Token::NONE;
}

bool Lexer::parseLiteralChar(int32_t chc)
{
  int32_t ch = nextChar();
  if (ch != chc)
  {
    // will be an error
    return false;
  }
  pushToToken(ch);
  return true;
}

bool Lexer::parseChar(CharacterClass cc)
{
  int32_t ch = nextChar();
  if (!isCharacterClass(ch, cc))
  {
    // will be an error
    return false;
  }
  pushToToken(ch);
  return true;
}

bool Lexer::parseNonEmptyCharList(CharacterClass cc)
{
  // must contain at least one character
  int32_t ch = nextChar();
  if (!isCharacterClass(ch, cc))
  {
    // will be an error
    return false;
  }
  pushToToken(ch);
  parseCharList(cc);
  return true;
}

void Lexer::parseCharList(CharacterClass cc)
{
  int32_t ch;
  for (;;)
  {
    ch = nextChar();
    if (!isCharacterClass(ch, cc))
    {
      // failed, we are done, put the character back
      saveChar(ch);
      return;
    }
    pushToToken(ch);
  }
}

Token Lexer::tokenizeCurrentSymbol() const
{
  Assert(!d_token.empty());
  switch (d_token[0])
  {
    case '-':
    {
      if (d_token.size()>=2)
      {
        // reparse as a negative numeral, rational or decimal
        Token ret = Token::INTEGER_LITERAL;
        for (size_t i=1, tsize = d_token.size(); i<tsize; i++)
        {
          if (isCharacterClass(d_token[i], CharacterClass::DECIMAL_DIGIT))
          {
            continue;
          }
          else if (i+1<tsize && ret==Token::INTEGER_LITERAL)
          {
            if (d_token[i]=='.')
            {
              ret = Token::DECIMAL_LITERAL;
              continue;
            }
            else if (d_token[i]=='/')
            {
              ret = Token::RATIONAL_LITERAL;
              continue;
            }
          }
          return Token::SYMBOL;
        }
        return ret;
      }
    }
      break;
    case 'a':
      if (d_token.size()>=4 && d_token[1] == 'l' && d_token[2] == 'f' && d_token[3] == '.')
      {
        if (d_token.size()==9 && d_token[4]=='m' && d_token[5]=='a' &&
            d_token[6]=='t' && d_token[7]=='c' && d_token[8]=='h')
        {
          // alf.match
          return Token::EVAL_MATCH;
        }
        else if (d_token.size()==10 && d_token[4]=='d' && d_token[5]=='e' &&
                 d_token[6]=='f' && d_token[7]=='i' && d_token[8]=='n' &&
                 d_token[9]=='e')
        {
          // alf.define
          return Token::EVAL_DEFINE;
        }
      }
      break;
    case 'p':
      if (d_token.size() == 3 && d_token[1] == 'a' && d_token[2] == 'r')
      {
        return Token::PAR;
      }
      break;
    case 'l':
      // only lex let if option is true (d_lexLet)
      if (d_lexLet && d_token.size() == 3 && d_token[1] == 'e' && d_token[2] == 't')
      {
        return Token::LET;
      }
      break;
    case 'B':
      if (d_token.size() == 4 && d_token[1] == 'o' && d_token[2] == 'o' && d_token[3] == 'l')
      {
        return Token::BOOL_TYPE;
      }
      break;
    case 'T':
      if (d_token.size() == 4 && d_token[1] == 'y' && d_token[2] == 'p' && d_token[3] == 'e')
      {
        return Token::TYPE;
      }
      break;
    default: break;
  }
  // otherwise not a special symbol
  return Token::SYMBOL;
}

}  // namespace alfc
