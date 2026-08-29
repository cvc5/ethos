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
  /** The deep embedding of the term is a proof-checker rule. */
  CHECKER_RULE,
  /** The deep embedding of the term is a proof-checker command. */
  CHECKER_CMD,
  /**
   * The deep embedding of the term is a datatype declared by a
   * $native_embed_eo type in the Eunoia templates. Its embedded name is
   * carried by that application; its constructors are static in the backend
   * templates. Similarly for the _smt and _checker variants below, which
   * additionally mark the term as belonging to the SMT-LIB model semantics
   * (see isSmtMetaKind) resp. the proof checker (see isCheckerMetaKind).
   */
  EO_EMBED,
  /** Datatype declared by a $native_embed_smt type. */
  SMT_EMBED,
  /** Datatype declared by a $native_embed_checker type. */
  CHECKER_EMBED,
  /** No meta-kind context. */
  NONE
};
/** Get a human-readable name for the meta-kind k, e.g. "SMT_TYPE". */
std::string metaKindToString(MetaKind k);
/**
 * Get the symbol-name prefix associated with meta-kind k, e.g. "eo." for
 * EUNOIA or "vsm." for SMT_VALUE. Returns a placeholder string for kinds
 * that have no dedicated prefix.
 */
std::string metaKindToPrefix(MetaKind k);
/** Return true if k is one of the SMT-LIB meta-kinds. */
bool isSmtMetaKind(MetaKind k);
/** Return true if k is one of the proof-checker meta-kinds. */
bool isCheckerMetaKind(MetaKind k);
/** Return true if k is one of the $native_embed_* meta-kinds. */
bool isEmbedMetaKind(MetaKind k);

/**
 * The prefix of the name of a "parse definition".
 *
 * A define command in the input introduces an identifier that is inlined by
 * the parser, so it has no counterpart in the compiled signature. It may
 * however occur in a proof, which means the generated proof parser still has
 * to be able to resolve it. The desugar stage therefore re-emits every
 * definition it can under this prefix, except that by convention a definition
 * whose name begins with "$" is a helper of the signature itself and is not
 * preserved, since a proof never mentions one. Each stage after desugaring reparses
 * the definition, which is how its body is compiled along with the rest of the
 * signature, but otherwise ignores it: a parse definition never contributes to
 * a verification condition or to the generated proof checker. The Lean backend
 * is the only consumer, which turns the definitions back into the tables of
 * the generated parser (see LeanMetaReduce::finalizeParser).
 */
const std::string& getParseDefPrefix();
/** Return true if name is the name of a parse definition. */
bool isParseDefName(const std::string& name);
/**
 * Return the name of the parse definition for the definition named name, i.e.
 * name prefixed by getParseDefPrefix().
 */
std::string mkParseDefName(const std::string& name);
/**
 * Return the name in the input of the parse definition named name, i.e. name
 * with getParseDefPrefix() removed. Requires isParseDefName(name).
 */
std::string getParseDefSurfaceName(const std::string& name);

/**
 * The text with the lines that are notes of the resource taken out, i.e.
 * those whose comment opens with a `$`: `-- $` where the resource is Lean and
 * `; $` where it is SMT-LIB.
 *
 * What a resource says about the tags it carries, or about why what it holds
 * is written there rather than where it belongs, is said to whoever edits the
 * resource. What it renders is read by someone else, who is owed the
 * definitions and not the reasons a compiler had for putting them there.
 */
std::string dropResourceNotes(const std::string& text);

/**
 * The text with no line ending in a blank.
 *
 * What a stage writes is compared byte for byte with what is checked in, so
 * nothing may end a line that a reader cannot see. A comment taken off the end
 * of a line is where such a blank comes from: the space that stood before the
 * `;` stays behind once the comment is gone.
 */
std::string rtrimLines(const std::string& text);

}  // namespace ethos

#endif
