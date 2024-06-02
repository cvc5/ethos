/******************************************************************************
 * This file is part of the alfc project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef KIND_H
#define KIND_H

#include <sstream>
#include <string>

namespace alfc {

/**
 */
enum class Kind
{
  NONE = 0,
  
  // types
  TYPE,
  FUNCTION_TYPE,
  PROOF_TYPE,
  ABSTRACT_TYPE,
  BOOL_TYPE,
  QUOTE_TYPE,
  OPAQUE_TYPE, // an argument marked :opaque, temporary during parsing
  
  // terms
  APPLY,
  LAMBDA,
  TUPLE,
  NULL_EXPR,
  PROGRAM,
  AS,
  PARAMETERIZED,
  APPLY_OPAQUE,

  // symbols
  PARAM,
  CONST,
  PROGRAM_CONST,
  PROOF_RULE,
  VARIABLE,
  ORACLE,

  // literals
  BOOLEAN,
  NUMERAL,
  DECIMAL,
  RATIONAL,
  HEXADECIMAL,
  BINARY,
  STRING,

  // operations on literals
  // core
  EVAL_IS_EQ,
  EVAL_IF_THEN_ELSE,
  EVAL_REQUIRES,
  EVAL_HASH,
  EVAL_VAR,
  EVAL_TYPE_OF,
  EVAL_NAME_OF,
  EVAL_COMPARE,
  // lists
  EVAL_NIL,
  EVAL_CONS,
  // boolean
  EVAL_NOT,
  EVAL_AND,
  EVAL_OR,
  EVAL_XOR,
  // arithmetic
  EVAL_ADD,
  EVAL_NEG,
  EVAL_MUL,
  EVAL_INT_DIV,
  EVAL_INT_MOD,
  EVAL_RAT_DIV,
  EVAL_IS_NEG,
  // strings
  EVAL_LENGTH,
  EVAL_CONCAT,
  EVAL_EXTRACT,
  EVAL_FIND,
  // conversions
  EVAL_TO_INT,
  EVAL_TO_RAT,
  EVAL_TO_BIN,
  EVAL_TO_STRING
};

/** Print a kind to the stream, for debugging */
std::ostream& operator<<(std::ostream& o, Kind k);

std::string kindToTerm(Kind k);

/** */
bool isSymbol(Kind k);
/** */
bool isLiteral(Kind k);
/** */
bool isLiteralOp(Kind k);
/** Is k a list literal operator? */
bool isListLiteralOp(Kind k);

}  // namespace alfc

#endif /* KIND_H */
