/******************************************************************************
 * This file is part of the ethos project.
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

namespace ethos {

/**
 */
enum class Kind
{
  NONE = 0,

  // types
  TYPE,
  FUNCTION_TYPE,
  PROGRAM_TYPE,
  PROOF_TYPE,
  BOOL_TYPE,
  QUOTE_TYPE,

  // terms
  APPLY,
  LAMBDA,
  TUPLE,
  PROGRAM,
  AS,         // (eo::as t T), where T is the type of t
  AS_RETURN,  // SMT-LIB (as t T), where T is the return type of t
  PARAMETERIZED,
  APPLY_OPAQUE,
  ANNOT_PARAM,  // a parameter with non-ground type that appears in type
                // checking
  ANY,          // atomic term standing for an unknown, treated as non-ground
                // and evaluatable.

  // symbols
  PARAM,
  CONST,
  BUILTIN_CONST,  // used for e.g. _, ->, eo::*, as, etc. which are temporary
                  // during parsing only
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
  EVAL_IS_OK,
  EVAL_IS_EQ,
  EVAL_IF_THEN_ELSE,
  EVAL_REQUIRES,
  EVAL_HASH,
  EVAL_VAR,
  EVAL_TYPE_OF,
  EVAL_NAME_OF,
  EVAL_COMPARE,
  // testers
  EVAL_IS_Z,
  EVAL_IS_Q,
  EVAL_IS_BIN,
  EVAL_IS_STR,
  EVAL_IS_BOOL,
  EVAL_IS_VAR,
  // equality
  EVAL_EQ,
  // lists
  EVAL_NIL,
  EVAL_CONS,
  EVAL_LIST_LENGTH,
  EVAL_LIST_CONCAT,
  EVAL_LIST_NTH,
  EVAL_LIST_FIND,
  EVAL_LIST_ERASE,
  EVAL_LIST_ERASE_ALL,
  EVAL_LIST_REV,
  EVAL_LIST_SETOF,
  EVAL_LIST_MINCLUDE,
  EVAL_LIST_MEQ,
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
  EVAL_GT,
  // strings
  EVAL_LENGTH,
  EVAL_CONCAT,
  EVAL_EXTRACT,
  EVAL_FIND,
  // conversions
  EVAL_TO_INT,
  EVAL_TO_RAT,
  EVAL_TO_BIN,
  EVAL_TO_STRING,
  // datatypes
  EVAL_DT_CONSTRUCTORS,
  EVAL_DT_SELECTORS
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

}  // namespace ethos

#endif /* KIND_H */
