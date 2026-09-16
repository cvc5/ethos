/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef PLUGIN_NATIVE_LAYER_H
#define PLUGIN_NATIVE_LAYER_H

#include <map>
#include <string>
#include <vector>

namespace ethos {

/**
 * The native layer of a backend: the definitions its generated text is
 * allowed to call and no compiler writes, and the part of them a compilation
 * of an input reaches.
 *
 * A layer is a configuration set -- plugins/lean_meta/lean.eos for the Lean
 * backend, plugins/smt_meta/smt-vc.eos for the SMT-LIB one -- which
 * tools/eoc/sem_compile.py compiles to the file read here. The line that
 * opens a block says everything a stage has to know about it:
 *
 *   <comment> $native <name> <needs> <calls>...
 *
 * <name> is what the block defines and what a signature may reach, <needs>
 * the narrowest scope it can come out in, and <calls> the rest of the layer
 * its text names, which is what the closure is taken over. A block is
 * everything under that line, its own comment included, up to the line that
 * opens the next. One further line, `<comment> $native-keep <name>...`, names
 * what is kept whatever an input reaches, which is what the resources of the
 * stage name themselves. See render_native in sem_compile.py.
 *
 * What the stage adds is which of it an input reaches: a name of the layer
 * reaches generated text only by being printed into it, so a stage notes each
 * as it prints it, against the scope of the module the text comes out in.
 * Nothing is read back out of what the stage wrote.
 */
class NativeLayer
{
 public:
  /**
   * Read the layer compiled to path.
   *
   * `comment` opens a comment in the language the layer is written in, e.g.
   * `--` for Lean and `;` for SMT-LIB. `top` is the scope every module of the
   * backend sees, which is where a block that two of them reach comes out and
   * the only scope a backend that writes one module has.
   */
  NativeLayer(const std::string& path,
              const std::string& comment,
              const std::string& top);
  /**
   * Note that the module of scope `scope` names n, which is what asks for the
   * block defining n and for everything that block calls. A name the layer
   * does not define is one a module writes for itself and is nothing to
   * place.
   *
   * Where a block comes out is the demand for it: a block two modules reach
   * comes out in the scope they share, which is the top one, and a block that
   * one scope alone can hold comes out there whatever reaches it.
   */
  void use(const std::string& n, const std::string& scope);
  /** As above, from the scope every module sees. */
  void use(const std::string& n);
  /** The part of the layer that comes out in scope, in the layer's order. */
  std::string defs(const std::string& scope) const;

 private:
  /** One block of the layer, as the line that opens it says it. */
  struct Def
  {
    /** What it defines, and what a signature may reach. */
    std::string d_name;
    /** The narrowest scope it can come out in, i.e. the one its text names. */
    std::string d_needs;
    /** The rest of the layer it calls, which the closure is taken over. */
    std::vector<std::string> d_deps;
    /** The text it is, carried as it stands. */
    std::string d_text;
  };
  /** The scope every module sees, see the constructor. */
  std::string d_top;
  /** The layer, in the order it gives its blocks. */
  std::vector<Def> d_defs;
  /** The block that defines each name. */
  std::map<std::string, size_t> d_of;
  /** The blocks the compilation reached, and the scope each comes out in. */
  std::map<std::string, std::string> d_at;
};

}  // namespace ethos

#endif
