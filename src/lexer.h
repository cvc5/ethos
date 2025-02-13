/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef LEXER_H
#define LEXER_H

#include <array>
#include <cstdint>
#include <fstream>
#include <iosfwd>
#include <string>
#include <vector>

#include "base/check.h"
#include "input.h"
#include "tokens.h"

namespace ethos {

/** A location for tracking parse errors */
struct Location
{
  Location() : d_line(1), d_column(1) {}
  uint32_t d_line;
  uint32_t d_column;
};
std::ostream& operator<<(std::ostream& o, const Location& l);

/** A span for tracking parse errors */
struct Span
{
  Location d_start;
  Location d_end;
};
std::ostream& operator<<(std::ostream& o, const Span& l);

#define INPUT_BUFFER_SIZE 32768

/**
 */
class Lexer
{
 public:
  Lexer(bool lexLet);
  virtual ~Lexer() {}
  /**
   * Initialize the lexer to generate tokens from stream input.
   * @param input The input stream
   * @param inputName The name for debugging
   */
  void initialize(Input* input, const std::string& inputName);
  /**
   * String corresponding to the last token (old top of stack). This is only
   * valid if no tokens are currently peeked.
   */
  const char* tokenStr() const;
  /** Advance to the next token (pop from stack) */
  Token nextToken();
  /** Add a token back into the stream (push to stack) */
  Token peekToken();
  /** Expect a token `t` as the next one. Error o.w. */
  void eatToken(Token t);
  /**
   * Expect a token `t` or `f` as the next one, or throw a parse error
   * otherwise. Return true if `t`.
   */
  bool eatTokenChoice(Token t, Token f);
  /** reinsert token, read back first in, last out */
  void reinsertToken(Token t);
  /** Used to report warnings, with the current source location attached. */
  void warning(const std::string&);
  /** Used to report errors, with the current source location attached. */
  void parseError(const std::string&, bool eofException = false);
  /** Error. Got `t`, expected `info`. */
  void unexpectedTokenError(Token t, const std::string& info);

 protected:
  // -----------------
  /** Compute the next token by reading from the stream */
  Token nextTokenInternal();
  /** Get the next character */
  int32_t readNextChar()
  {
    if (d_bufferPos < d_bufferEnd)
    {
      d_ch = d_buffer[d_bufferPos];
      d_bufferPos++;
    }
    else if (d_isInteractive)
    {
      d_ch = d_istream->get();
    }
    else
    {
      d_istream->read(d_buffer, INPUT_BUFFER_SIZE);
      d_bufferEnd = static_cast<size_t>(d_istream->gcount());
      if (d_bufferEnd == 0)
      {
        d_ch = EOF;
        d_bufferPos = 0;
      }
      else
      {
        d_ch = d_buffer[0];
        d_bufferPos = 1;
      }
    }
    return d_ch;
  }
  /** Get the next character */
  int32_t nextChar()
  {
    int32_t res;
    if (d_peekedChar)
    {
      res = d_chPeeked;
      d_peekedChar = false;
    }
    else
    {
      res = readNextChar();
      if (res == '\n')
      {
        d_span.d_end.d_line++;
        d_span.d_end.d_column = 0;
      }
      else
      {
        d_span.d_end.d_column++;
      }
    }
    return res;
  }
  /** Save character */
  void saveChar(int32_t ch)
  {
    Assert(!d_peekedChar);
    d_peekedChar = true;
    d_chPeeked = ch;
  }
  // -----------------
  /** Used to initialize d_span. */
  void initSpan();
  /** Sets the spans start to its current end. */
  void bumpSpan()
  {
    d_span.d_start.d_line = d_span.d_end.d_line;
    d_span.d_start.d_column = d_span.d_end.d_column;
  }
  /** Add columns or lines to the end location of the span. */
  void addColumns(uint32_t columns) { d_span.d_end.d_column += columns; }
  void addLines(uint32_t lines)
  {
    d_span.d_end.d_line += lines;
    d_span.d_end.d_column = 0;
  }
  /** Span of last token pulled from underlying lexer (old top of stack) */
  Span d_span;
  /** Name of current input, for debugging */
  std::string d_inputName;
  /**
   * The peeked stack. When we peek at the next token, it is added to this
   * vector. When we read a token, if this vector is non-empty, we return the
   * back of it and pop.
   */
  std::vector<Token> d_peeked;

 private:
  /** The input */
  std::istream* d_istream;
  /** Are we lexing "let"? */
  bool d_lexLet;
  /** True if the input stream is interactive */
  bool d_isInteractive;
  /** The current buffer */
  char d_buffer[INPUT_BUFFER_SIZE];
  /** The position in the current buffer we are reading from */
  size_t d_bufferPos;
  /** The size of characters in the current buffer */
  size_t d_bufferEnd;
  /** The current character we read. */
  int32_t d_ch;
  /** True if we have a saved character that has not been consumed yet. */
  bool d_peekedChar;
  /** The saved character. */
  int32_t d_chPeeked;
  /**
   * Computes the next token and adds its characters to d_token. Does not
   * null terminate.
   */
  Token computeNextToken();
  /** Push a character to the stored token */
  void pushToToken(int32_t ch)
  {
    Assert(ch != EOF);
    d_token.push_back(static_cast<char>(ch));
  }
  //----------- Utilities for parsing the current character stream
  enum class CharacterClass
  {
    NONE = 0,
    WHITESPACE = (1 << 0),
    DECIMAL_DIGIT = (1 << 1),
    HEXADECIMAL_DIGIT = (1 << 2),
    BIT = (1 << 3),
    SYMBOL_START = (1 << 4),
    SYMBOL = (1 << 5),
  };
  /** The set of non-letter/non-digit characters that may occur in keywords. */
  inline static const std::string s_extraSymbolChars = "+-/*=%?!.$_~&^<>@";
  /** parse <c>, return false if <c> is not ch. */
  bool parseLiteralChar(int32_t ch);
  /** parse <c>, return false if <c> is not from cc */
  bool parseChar(CharacterClass cc);
  /** parse <c>+ from cc, return false if the next char is not from cc. */
  bool parseNonEmptyCharList(CharacterClass cc);
  /** parse <c>* from cc. */
  void parseCharList(CharacterClass cc);
  /** Return true if ch is in character class cc */
  bool isCharacterClass(int32_t ch, CharacterClass cc) const
  {
    return d_charClass[static_cast<uint8_t>(ch)] & static_cast<uint8_t>(cc);
  }
  //----------- Utilizes for tokenizing d_token
  /**
   * Tokenize current symbol stored in d_token.
   *
   * This method changes the string in d_token into the appropriate token.
   * Otherwise, we return Token::SYMBOL.
   *
   * The list of all simple symbols that are converted by this method.
   *   as, par, let, match, Constant, Variable, _
   *
   * We don't handle command tokens here.
   */
  Token tokenizeCurrentSymbol() const;
  /** The characters in the current token */
  std::vector<char> d_token;
  /** The character classes. */
  std::array<uint8_t, 256> d_charClass{};  // value-initialized to 0
};

}  // namespace ethos

#endif
