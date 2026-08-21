/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef PLUGIN_MODEL_SMT_EO_REDUCE_SPEC_H
#define PLUGIN_MODEL_SMT_EO_REDUCE_SPEC_H

#include <map>
#include <string>
#include <vector>

namespace ethos {

/**
 * One case of $eo_to_smt or $eo_to_smt_type read from a reduction file, i.e.
 * one way of eliminating a Eunoia symbol on the way to the SMT-LIB term layer.
 */
struct EoReduceCase
{
  /** The Eunoia symbol this case reduces, i.e. the head of its pattern. */
  std::string d_symbol;
  /** The pattern, verbatim, e.g. "(exists $eo_List_nil x1)". */
  std::string d_pattern;
  /** The right hand side of the case, verbatim. */
  std::string d_ret;
  /** The number of arguments of the pattern. */
  size_t d_arity;
  /**
   * True if the pattern is (<symbol> x1 ... xn), or the atom <symbol>, that
   * is, if this case applies to every application of the symbol. Otherwise the
   * case is for a special shape of an argument and is emitted, verbatim,
   * before the symbol's own case.
   */
  bool d_generic;
  /** True if this is a case of $eo_to_smt_type instead of $eo_to_smt. */
  bool d_isType;
  /**
   * The names of the auxiliary programs of the file that this case requires,
   * that is, those it mentions, together with those they mention in turn,
   * ordered as they occur in the file.
   */
  std::vector<std::string> d_aux;
};

/**
 * The contents of a Eunoia-to-SMT reduction file, e.g.
 * plugins/model_smt/eo_to_smt_cpc.eo, which specifies how the symbols of a
 * calculus are reduced by the $eo_to_smt and $eo_to_smt_type programs of the
 * generated model semantics.
 *
 * The file is read as Eunoia syntax but is not interpreted: the pattern of a
 * case determines the symbol it applies to and the number of arguments it
 * takes, and everything else is carried along as the verbatim source text of
 * the file, to be copied into the generated program.
 */
class EoReduceSpec
{
 public:
  /**
   * Parse the reduction file whose contents are s. Returns true if successful,
   * and otherwise sets err to a description of what went wrong.
   */
  bool parse(const std::string& s, std::string& err);
  /** The cases of the file, in the order they occur. */
  const std::vector<EoReduceCase>& getCases() const;
  /**
   * The verbatim source text of the auxiliary program named name, which is
   * required to be one of the names occurring in the d_aux of a case.
   */
  const std::string& getAuxProgram(const std::string& name) const;

 private:
  /** The cases of $eo_to_smt and $eo_to_smt_type, in the order of the file. */
  std::vector<EoReduceCase> d_cases;
  /** Maps the name of an auxiliary program to its verbatim source text. */
  std::map<std::string, std::string> d_auxText;
  /** The names of the auxiliary programs, in the order of the file. */
  std::vector<std::string> d_auxOrder;
};

}  // namespace ethos

#endif
