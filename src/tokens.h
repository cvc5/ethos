/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef TOKENS_H
#define TOKENS_H

#include <sstream>
#include <string>

namespace ethos {

/**
 */
enum class Token
{
  EOF_TOK = 0,
  ASSERT,
  ASSUME,
  ASSUME_PUSH,
  ATTRIBUTE,
  BOOL_TYPE,
  BINARY_LITERAL,
  CHECK_SAT,
  CHECK_SAT_ASSUMING,
  DECIMAL_LITERAL,
  DECLARE_CONST,
  DECLARE_CONSTS,
  DECLARE_DATATYPE,
  DECLARE_DATATYPES,
  DECLARE_FUN,
  DECLARE_PARAMETERIZED_CONST,
  DECLARE_ORACLE_FUN,
  DECLARE_RULE,
  DECLARE_SORT,
  DECLARE_TYPE,
  DECLARE_VAR,
  DEFINE,
  DEFINE_CONST,
  DEFINE_FUN,
  DEFINE_SORT,
  DEFINE_TYPE,
  ECHO,
  EVAL_DEFINE,  // eo::define
  EXIT,
  HEX_LITERAL,
  INCLUDE,
  INTEGER_LITERAL,
  KEYWORD,
  LET,
  LPAREN,
  NUMERAL,
  PAR,
  POP,
  PROGRAM,
  PROOF,
  PROOF_TYPE,
  PUSH,
  QUOTED_SYMBOL,
  RATIONAL_LITERAL,
  REFERENCE,
  RESET,
  RPAREN,
  SET_INFO,
  SET_LOGIC,
  SET_OPTION,
  STEP,
  STEP_POP,
  STRING_LITERAL,
  SYMBOL,
  TYPE,
  UNTERMINATED_QUOTED_SYMBOL,
  UNTERMINATED_STRING_LITERAL,
  NONE
};

/** Print a token to the stream, for debugging */
std::ostream& operator<<(std::ostream& o, Token t);

}  // namespace ethos

#endif /* TOKENS_H */
