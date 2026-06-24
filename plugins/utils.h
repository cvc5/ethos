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
  /** The deep embedding of the term is a Eunoia term. */
  EUNOIA,
  /** The deep embedding of the term is a Eunoia datatype. */
  DATATYPE,
  /** The deep embedding of the term is a Eunoia datatype constructor. */
  DATATYPE_CONSTRUCTOR,
  /** The deep embedding of the term is an SMT-LIB model. */
  SMT_MODEL,
  /** The deep embedding of the term is a list of datatype references. */
  SMT_REFLIST,
  /** The deep embedding of the term is an SMT-LIB term. */
  SMT,
  /** The deep embedding of the term is an SMT-LIB type. */
  SMT_TYPE,
  /** The deep embedding of the term is an SMT-LIB value. */
  SMT_VALUE,
  /** The deep embedding of the term is an SMT-LIB map value. */
  SMT_MAP,
  /** The deep embedding of the term is an SMT-LIB sequence value. */
  SMT_SEQ,
  /** The deep embedding of the term is a builtin SMT-LIB term. */
  SMT_BUILTIN,
  /** The deep embedding of the term is a builtin SMT-LIB datatype (e.g. Nat). */
  SMT_BUILTIN_DATATYPE,
  /** The deep embedding of the term is a proof. */
  PROOF,
  /** The deep embedding of the term is an SMT-LIB datatype. */
  SMT_DATATYPE,
  /** The deep embedding of the term is an SMT-LIB datatype constructor. */
  SMT_DATATYPE_CONSTRUCTOR,
  /** The deep embedding of the term is a proof-checker rule. */
  CHECKER_RULE,
  /** The deep embedding of the term is a proof-checker state. */
  CHECKER_STATE,
  /** The deep embedding of the term is a proof-checker state object. */
  CHECKER_STATE_OBJ,
  /** The deep embedding of the term is a proof-checker command. */
  CHECKER_CMD,
  /** The deep embedding of the term is a list of proof-checker commands. */
  CHECKER_CMD_LIST,
  /** The deep embedding of the term is a proof-checker index. */
  CHECKER_INDEX,
  /** The deep embedding of the term is a list of proof-checker indices. */
  CHECKER_INDEX_LIST,
  /** The deep embedding of the term is a list of proof-checker arguments. */
  CHECKER_ARG_LIST,
  /** No meta-kind context. */
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
