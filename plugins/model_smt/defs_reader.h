/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#ifndef PLUGINS__MODEL_SMT__DEFS_READER_H
#define PLUGINS__MODEL_SMT__DEFS_READER_H

#include <map>
#include <set>
#include <string>
#include <vector>

namespace ethos {

/**
 * One aggregate of the deep embedding, as the head of a generated signature
 * declares it:
 *
 *   ; $eoc-aggregate <name> <case> <into> [whole]
 *
 * A symbol says one case of an aggregate and the compiler writes a program for
 * it, named <case> and then the symbol; this says which aggregate that program
 * feeds and where what is taken from it is written. Nothing here knows any
 * aggregate by name: the lines are compiled from
 * plugins/model_smt/model_smt.eos, which is where one is to be changed or
 * added, and adding one asks nothing of this stage.
 */
struct DefsAggregate
{
  /**
   * The aggregate the cases are spliced into, i.e. what the head of a case is
   * rewritten to; where the program is emitted whole, the name it comes out
   * under.
   */
  std::string d_name;
  /** What a symbol's case is named, up to the symbol. */
  std::string d_case;
  /** The marker of the template what is taken from it is written at. */
  std::string d_into;
  /**
   * Whether the program is emitted whole under d_name rather than its cases
   * being spliced into it. The nil of an n-ary symbol is the one such: the
   * desugar stage asks for it by name rather than taking a case of it.
   */
  bool d_whole = false;
};

/**
 * The programs written over values that the cases of an aggregate hand their
 * work to, as the head declares them:
 *
 *   ; $eoc-helper <case> <forward>
 *
 * One stands with the other helpers, and is forward declared at <forward>,
 * ahead of the aggregate, since a case of one may name another whichever of
 * them the file writes first.
 */
struct DefsHelper
{
  /** What one is named, up to the symbol. */
  std::string d_case;
  /** The marker of the template the forward declarations are written at. */
  std::string d_forward;
};

/**
 * One datatype of the embedding, i.e. one of the things a value is built over
 * rather than one of the values: a regular language is one. What a constructor
 * of it is called and where its declarations are written is what the head of
 * the file says, so this stage knows none of them by name and adding one asks
 * nothing of it. Declared in plugins/model_smt/model_smt.eos.
 */
struct DefsEmbedDatatype
{
  /** The constant a constructor of it is declared as, up to the name. */
  std::string d_cons;
  /** The macro that applies it, up to the name. */
  std::string d_macro;
  /** The marker of the template the declarations are written at. */
  std::string d_into;
};

/**
 * What one symbol of a signature contributes to the generated file, i.e. the
 * block a `; -- X` line opens in a definitions file, see
 * tools/eoc/out/smt_defs.eo and the signature of the input given with
 * --semantics, e.g. tools/eoc/out/user_defs.eo.
 *
 * A block is read as *text* rather than as terms. What it says is copied into
 * the generated file as it stands, which is what keeps the definitions of the
 * embedding it names, e.g. $vsm_bool, from being expanded on the way; a term
 * would have to be printed back, and printing expands them.
 */
struct DefsBlock
{
  /** The symbol the block is of, as its `; -- X` line names it. */
  std::string d_sym;
  /** The names it defines. */
  std::set<std::string> d_defs;
  /** The names it uses that it does not define. */
  std::set<std::string> d_uses;
  /**
   * Whether the block stands whether or not the input declares its symbol,
   * which `(echo "eoc-keep symbol X")` is what says. A few symbols are the
   * embedding's own rather than any one calculus's -- ite and =, which the
   * hand-written proofs about the generated Lean are written over -- and a
   * calculus trimmed to a handful of rules would otherwise leave one out.
   * See DefsFile::select.
   */
  bool d_keep = false;
  /**
   * Whether the block is of a term the embedding builds itself -- a literal,
   * i.e. one built over a native rather than over terms -- rather than of a
   * symbol of the signature written over them. A block of one is named after
   * the constructor it declares, which is what says so: `$emb_sm.Binary`
   * rather than a symbol's own name. Its constructor stands with the terms of
   * the embedding, before the symbols, so that the order of them is the same
   * whatever a calculus declares, see ModelSmt::finalize.
   */
  bool d_literal = false;
  /** The constructor of the embedding for the symbol, and the macro. */
  std::vector<std::string> d_cons;
  /** The same, where the block is of a type rather than of a symbol. */
  std::vector<std::string> d_typeCons;
  /** The same, where it is of a value. */
  std::vector<std::string> d_valueCons;
  /**
   * The auxiliary programs the block holds, i.e. what its cases call rather
   * than what they contribute, in the order the block writes them. They are
   * one stream because they are one dependency graph: the evaluator of a
   * sequence asks for the type of one, and the type of a sequence value is
   * worked out over the values it holds, so neither family can be said to come
   * first. What orders them is the signature itself, which writes a program
   * after the ones it calls; see $SMT_HELPER_PROGS$ in
   * plugins/model_smt/model_smt.eo.
   */
  std::vector<std::string> d_helperProgs;
  /** The same, for the programs written over the transformation. */
  std::vector<std::string> d_eoAux;
  /**
   * The programs that say whether a value of a shape is canonical, which stand
   * with $smtx_value_canonical rather than with the other helpers: they call
   * $smtx_type_default and $smtx_is_finite_type, which are written after
   * those. A program whose name ends in `_canonical` is one.
   */
  std::vector<std::string> d_canonicalAux;
  /**
   * What the block contributes to the aggregates, keyed by the marker of the
   * template it is written at, see DefsAggregate. A case has its head
   * rewritten from the name of the per-symbol program to the name of the
   * aggregate it feeds; a program the head declares whole, and a forward
   * declaration of a helper, stand as they are.
   *
   * Which markers there are is read off the file rather than known here, so a
   * signature that declares one more aggregate contributes to one more marker
   * and nothing in this stage says which.
   */
  std::map<std::string, std::vector<std::string>> d_at;
};

/**
 * A definitions file, i.e. a signature written directly in the deep embedding.
 * Reading one gives the blocks it holds and says which block defines what, so
 * that the blocks a signature needs can be taken and the rest left, see
 * DefsFile::select.
 */
class DefsFile
{
 public:
  /**
   * Read the file at path. Returns false if it could not be read or contained
   * no definition blocks.
   */
  bool read(const std::string& path);
  /** The aggregates the head of the file declares. */
  const std::vector<DefsAggregate>& getAggregates() const
  {
    return d_aggregates;
  }
  /** The datatypes the head of the file declares, see DefsEmbedDatatype. */
  const std::vector<DefsEmbedDatatype>& getEmbedDatatypes() const
  {
    return d_embedDatatypes;
  }
  /** The programs written over values it declares, see DefsHelper. */
  const std::vector<DefsHelper>& getHelpers() const { return d_helpers; }
  /**
   * The blocks whose symbol is in syms or that said `eoc-keep`, together with
   * every block those depend on, in the order the file gives them. A block
   * depends on the one that defines a name it uses, e.g. the value of div is
   * the value of div_total away from zero, so keeping div keeps div_total. A
   * block that defines one of names is kept as well, which is how a block of
   * another file is answered: the transformation of - names the constructor
   * of uneg, which the SMT-LIB file is what defines.
   */
  std::vector<const DefsBlock*> select(
      const std::set<std::string>& syms,
      const std::set<std::string>& names = {}) const;
  /** The names the blocks use that no block of this file defines. */
  std::set<std::string> externalUses(
      const std::vector<const DefsBlock*>& blocks) const;
  /** The blocks, in the order the file gives them. */
  const std::vector<DefsBlock>& getBlocks() const { return d_blocks; }

 private:
  /** Read one block from text, having already taken its symbol. */
  void addBlock(const std::string& sym, const std::string& text);
  /** Read what the head of the file declares, i.e. everything above the
   * first block. */
  void readHead(const std::string& head);
  /**
   * The aggregate a per-symbol program belongs to, or nullptr where the name
   * is of no aggregate. The longest case a name begins with is the one it
   * belongs to, which is what lets $eoc_transform_type_ stand beside
   * $eoc_transform_ whatever order the head declares them in.
   */
  const DefsAggregate* aggregateOf(const std::string& name) const;
  /** The same, for a program written over values. */
  const DefsHelper* helperOf(const std::string& name) const;
  /**
   * Put one form of a block into the stream its name says. It is what a
   * program is classified by, and what a helper written as a define rather
   * than as a program is classified by too, since neither is a constructor of
   * any family.
   */
  /** The datatype a name is a constructor of, or nullptr. */
  const DefsEmbedDatatype* embedDatatypeOf(const std::string& name) const;
  void classifyProgram(DefsBlock& b,
                       const std::string& f,
                       const std::string& name);
  std::vector<DefsBlock> d_blocks;
  /** What the head declares, longest case first, see aggregateOf. */
  std::vector<DefsAggregate> d_aggregates;
  /** The datatypes the head declares, see DefsEmbedDatatype. */
  std::vector<DefsEmbedDatatype> d_embedDatatypes;
  /** The same, for the programs written over values. */
  std::vector<DefsHelper> d_helpers;
  /** The block that defines each name. */
  std::map<std::string, size_t> d_owner;
};

/**
 * Order blocks by the input declaration order. Before each declared block,
 * recursively place any dependency block whose symbol is not itself declared.
 */
std::vector<const DefsBlock*> orderByDeclarations(
    const std::vector<const DefsBlock*>& blocks,
    const std::vector<std::string>& declarations);

}  // namespace ethos

#endif
