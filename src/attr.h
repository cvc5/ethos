/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef ATTR_H
#define ATTR_H

#include <sstream>
#include <string>

namespace ethos {

/**
 */
enum class Attr
{
  NONE = 0,

  VAR,
  IMPLICIT,
  REQUIRES,
  TYPE,
  // properties of rules
  SORRY,

  //------------------ below here is mutually exclusive?
  LIST,
  PROGRAM,
  ORACLE,
  BINDER,
  LET_BINDER,
  OPAQUE,

  // smt3 things that are not strictly supported
  SYNTAX,
  RESTRICT,

  // indicate how to construct proof rule steps.
  // A proof rule R maps to a tuple (P, A, C), where
  // - P is an n-ary operator set by :premise-list (default State::mkAny()),
  // - A indicates if R has been marked :assumption (default false),
  // - C indicates if R has been marked :conclusion-explicit (default false).
  PROOF_RULE,

  // indicate how to construct apps of function symbols
  RIGHT_ASSOC,
  LEFT_ASSOC,
  RIGHT_ASSOC_NIL,
  LEFT_ASSOC_NIL,
  CHAINABLE,
  PAIRWISE,

  // ambiguous functions e.g. set.empty which require annotations
  AMB,

  // datatypes
  DATATYPE,
  DATATYPE_CONSTRUCTOR,
  AMB_DATATYPE_CONSTRUCTOR,  // constructors requiring an opaque type argument
  CODATATYPE
};

/**
 * Is the Attr indicate that any number of children can be passed to the given
 * operator?
 */
bool isNAryAttr(Attr a);
/**
 * Is the Attr specifying a constructor kind?
 */
bool isConstructorKindAttr(Attr a);

/** Print a kind to the stream, for debugging */
std::ostream& operator<<(std::ostream& o, Attr a);

}  // namespace ethos

#endif /* ATTR_H */
