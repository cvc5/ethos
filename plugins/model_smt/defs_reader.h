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
 * plugins/model_smt/smt_defs.eo and plugins/model_smt/cpc_defs.eo.
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
  /** The constructor of the embedding for the symbol, and the macro. */
  std::vector<std::string> d_cons;
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
  /** Read the file at path. Returns false if it could not be read. */
  bool read(const std::string& path);
  /**
   * The blocks whose symbol is in syms, together with every block those
   * depend on, in the order the file gives them. A block depends on the one
   * that defines a name it uses, e.g. the value of div is the value of
   * div_total away from zero, so keeping div keeps div_total. A block that
   * defines one of names is kept as well, which is how a block of another
   * file is answered: the transformation of - names the constructor of uneg,
   * which the SMT-LIB file is what defines.
   */
  std::vector<const DefsBlock*> select(const std::set<std::string>& syms,
                                      const std::set<std::string>& names =
                                          {}) const;
  /** The names the blocks use that no block of this file defines. */
  std::set<std::string> externalUses(
      const std::vector<const DefsBlock*>& blocks) const;
  /** The blocks, in the order the file gives them. */
  const std::vector<DefsBlock>& getBlocks() const { return d_blocks; }
  /** True if some block is of the symbol sym. */
  bool hasSymbol(const std::string& sym) const;

 private:
  /** Read one block from text, having already taken its symbol. */
  void addBlock(const std::string& sym, const std::string& text);
  std::vector<DefsBlock> d_blocks;
  /** The block that defines each name. */
  std::map<std::string, size_t> d_owner;
};

}  // namespace ethos

#endif
