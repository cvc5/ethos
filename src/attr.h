/******************************************************************************
 * This file is part of the alfc project.
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

namespace alfc {

/**
 */
enum class Attr
{
  NONE = 0,
  
  VAR,
  IMPLICIT,
  REQUIRES,

  //------------------ below here is mutually exclusive?
  LIST,
  SYNTAX,
  PROGRAM,
  ORACLE,
  BINDER,
  
  // indicate how to construct proof rule steps
  PREMISE_LIST,

  // indicate how to construct apps of function symbols
  RIGHT_ASSOC,
  LEFT_ASSOC,
  RIGHT_ASSOC_NIL,
  LEFT_ASSOC_NIL,
  CHAINABLE,
  PAIRWISE,

  // datatypes
  DATATYPE,
  DATATYPE_CONSTRUCTOR,
  CODATATYPE
};

/** Print a kind to the stream, for debugging */
std::ostream& operator<<(std::ostream& o, Attr a);

}  // namespace alfc

#endif /* ATTR_H */
