/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#ifndef PLUGIN_UTILS_H
#define PLUGIN_UTILS_H

#include <string>

namespace ethos {

/**
 * Shared utilities for the experimental eoc meta-reduction plugins (see
 * MetaReducePlugin). The central definition is MetaKind, which classifies the
 * deep embedding of a term, together with helpers for naming and categorizing
 * these kinds.
 */

/**
 * Identifies the meta-level category of a term's deep embedding during
 * meta-reduction. Each constant declared by a plugin is classified into one of
 * these kinds, which determines how the term is embedded and printed, e.g. as a
 * Eunoia term, an SMT-LIB term/type/value, a datatype, or a proof-checker
 * construct.
 */
enum class MetaKind
{
  /** A context in which the deep embedding of the term is a Eunoia term */
  EUNOIA,
  /** A Eunoia datatype / datatype constructor */
  DATATYPE,
  DATATYPE_CONSTRUCTOR,
  /** smt model */
  SMT_MODEL,
  /** a list of references for datatypes */
  SMT_REFLIST,
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
  /** A builtin SMT-LIB datatype used in the final embedding, e.g. Nat */
  SMT_BUILTIN_DATATYPE,
  /** A proof */
  PROOF,
  // datatypes
  SMT_DATATYPE,
  SMT_DATATYPE_CONSTRUCTOR,
  // checker
  CHECKER_RULE,
  CHECKER_STATE,
  CHECKER_STATE_OBJ,
  CHECKER_CMD,
  CHECKER_CMD_LIST,
  CHECKER_INDEX,
  CHECKER_INDEX_LIST,
  CHECKER_ARG_LIST,
  /** No context */
  NONE
};
/** Get a human-readable name for the meta-kind k, e.g. "SMT_TYPE". */
std::string metaKindToString(MetaKind k);
/**
 * Get the symbol-name prefix associated with meta-kind k, e.g. "eo." for
 * EUNOIA or "edt." for DATATYPE. Returns a placeholder string for kinds that
 * have no dedicated prefix.
 */
std::string metaKindToPrefix(MetaKind k);
/** Return true if k is one of the SMT-LIB meta-kinds. */
bool isSmtMetaKind(MetaKind k);
/** Return true if k is one of the proof-checker (CHECKER_*) meta-kinds. */
bool isCheckerMetaKind(MetaKind k);

}  // namespace ethos

#endif
