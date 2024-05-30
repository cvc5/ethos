/******************************************************************************
 * This file is part of the alfc project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef PLUGIN_H
#define PLUGIN_H

#include <string>

#include "attr.h"
#include "expr.h"
#include "expr_info.h"
#include "util/filesystem.h"

namespace alfc {

/**
 * A plugin class. This is a virtual base class that receives callbacks from
 * the core of the ALFC checker.
 *
 * An example use of this class is to compile an ALF signature to C++.
 */
class Plugin
{
public:
  Plugin() {}
  virtual ~Plugin() {}
  /** Reset */
  virtual void reset() = 0;
  /** Push scope */
  virtual void pushScope() = 0;
  /** Pop scope */
  virtual void popScope() = 0;
  /** include file, if not already done */
  virtual void includeFile(const Filepath& s) = 0;
  /** Set type rule for literal kind k to t */
  virtual void setLiteralTypeRule(Kind k, const Expr& t) = 0;
  /** Called when expression e is bound to the given name */
  virtual void bind(const std::string& name, const Expr& e) = 0;
  /** Mark attributes */
  virtual void markConstructorKind(const Expr& v, Attr a, const Expr& cons) = 0;
  /** Mark oracle command */
  virtual void markOracleCmd(const Expr& v, const std::string& ocmd) = 0;
  /** Define program */
  virtual void defineProgram(const Expr& v, const Expr& prog) = 0;
  /** Define constructor */
  virtual void defineConstructor(const Expr& c, const std::vector<Expr>& sels) = 0;
  /** Define datatype */
  virtual void defineDatatype(const Expr& d, const std::vector<Expr>& cons) = 0;
  /** Finalize */
  virtual void finalize() = 0;
};

}  // namespace alfc

#endif /* STATE_H */
