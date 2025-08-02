/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#ifndef PLUGIN_SMT_META_UTILS_H
#define PLUGIN_SMT_META_UTILS_H

#include <string>

namespace ethos {

/**
 * The datatype we are at.
 */
enum class MetaKind
{
  /** A context in which the deep embedding of the term is a Eunoia term */
  EUNOIA,
  /** A context in which the deep embedding of the term is an SMT-LIB term */
  SMT,
  /** A context in which the deep embedding of the term is an SMT-LIB type */
  SMT_TYPE,
  /** A context in which the deep embedding of the term is an SMT-LIB value */
  SMT_VALUE,
  /** A context in which the term is an SMT-LIB map value */
  SMT_MAP,
  /** A context in which the term is an SMT-LIB sequence value */
  SMT_SEQ,
  /** A builtin SMT-LIB term context */
  SMT_BUILTIN,
  /** A program */
  PROGRAM,
  /** No context */
  NONE
};
std::string metaKindToString(MetaKind k);
std::string metaKindToPrefix(MetaKind k);
std::string metaKindToCons(MetaKind k);

}  // namespace ethos

#endif
