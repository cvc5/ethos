/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Assertion utility classes, functions and macros.
 */

#include "base/check.h"

#include <cstdlib>
#include <iostream>

namespace alfc {

FatalStream::FatalStream(const char* function, const char* file, int line) : d_abort(true)
{
  stream() << "Fatal failure within " << function << " at " << file << ":"
           << line << "\n";
}

FatalStream::~FatalStream()
{
  Flush();
  if (d_abort)
  {
    abort();
  }
  else
  {
    exit(1);
  }
}

std::ostream& FatalStream::stream() { return std::cerr; }

void FatalStream::Flush()
{
  stream() << std::endl;
  stream().flush();
}

}  // namespace alfc
