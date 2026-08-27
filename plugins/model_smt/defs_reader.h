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
 * What one symbol of a signature contributes to the generated file, i.e. the
 * block a `; -- X` line opens in a definitions file, see
 * tools/eoc/out/smt_defs.eo and the signature of the input given with
 * --signature, e.g. tools/eoc/out/user_defs.eo.
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
  /** The constructor of the embedding for the symbol, and the macro. */
  std::vector<std::string> d_cons;
  /** The same, where the block is of a type rather than of a symbol. */
  std::vector<std::string> d_typeCons;
  /** The auxiliary programs, by the stream each belongs to. */
  std::vector<std::string> d_typeofAux, d_evalProgs, d_eoAux;
  /**
   * What the *desugar* stage asks about the symbol rather than the model, i.e.
   * the program that decides whether a term is the nil of it.
   */
  std::vector<std::string> d_desugarAux;
  /** A forward declaration of each program of d_evalProgs. */
  std::vector<std::string> d_evalFwd;
  /**
   * The cases it contributes, with the head of each rewritten from the name of
   * the per-symbol program to the name of the aggregate it feeds.
   */
  std::vector<std::string> d_typeofCases, d_evalCases, d_transCases,
      d_transTypeCases;
  /** The same, for what a block of a type says about it. */
  std::vector<std::string> d_typeWfCases, d_typeBoundedCases,
      d_typeDefaultCases;
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
  std::vector<DefsBlock> d_blocks;
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
