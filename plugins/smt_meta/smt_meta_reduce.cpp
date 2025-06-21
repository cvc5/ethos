/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "smt_meta_reduce.h"

namespace ethos {

SmtMetaReduce::SmtMetaReduce(State& s) : d_state(s) {

}

SmtMetaReduce::~SmtMetaReduce() {}

void SmtMetaReduce::reset() {}

void SmtMetaReduce::pushScope() {}

void SmtMetaReduce::popScope() {}

void SmtMetaReduce::includeFile(const Filepath& s, bool isReference, const Expr& referenceNf) {}

void SmtMetaReduce::setLiteralTypeRule(Kind k, const Expr& t) {}

void SmtMetaReduce::bind(const std::string& name, const Expr& e) {}

void SmtMetaReduce::markConstructorKind(const Expr& v, Attr a, const Expr& cons) {}

void SmtMetaReduce::markOracleCmd(const Expr& v, const std::string& ocmd) {}

void SmtMetaReduce::defineProgram(const Expr& v, const Expr& prog) {
  std::cout << "Define program " << v << std::endl;
}

void SmtMetaReduce::finalize() {}

std::string toString() {

}

}  // namespace ethos
