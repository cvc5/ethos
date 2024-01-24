/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Tim King, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************
 *
 * Assertion utility classes, functions and macros.
 *
 * Assertion macros assert a condition and aborts() the process if the
 * condition is not satisfied. These macro leave a hanging ostream for the user
 * to specify additional information about the failure.
 *
 * Example usage:
 *   AlwaysAssert(x >= 0) << "x must be positive.";
 *
 * Assert is an AlwaysAssert that is only enabled in debug builds.
 *   Assert(pointer != nullptr);
 *
 * ALFC_FATAL() can be used to indicate unreachable code.
 *
 * Note: The AlwaysAssert and Assert macros are not safe for use in
 *       signal-handling code.
 */

#ifndef ALFC__CHECK_H
#define ALFC__CHECK_H

#include <cstdarg>
#include <ostream>

namespace alfc {

// Implementation notes:
// To understand FatalStream and OStreamVoider, it is useful to understand
// how a AlwaysAssert is structured. AlwaysAssert(cond) is roughly the following
// pattern:
//  cond ? (void)0 : OstreamVoider() & FatalStream().stream()
// This is a carefully crafted message to achieve a hanging ostream using
// operator precedence. The line `AlwaysAssert(cond) << foo << bar;` will bind
// as follows:
//  `cond ? ((void)0) : (OSV() & ((FS().stream() << foo) << bar));`
// Once the expression is evaluated, the destructor ~FatalStream() of the
// temporary object is then run, which abort()'s the process. The role of the
// OStreamVoider() is to match the void type of the true branch.

// Class that provides an ostream and whose destructor aborts! Direct usage of
// this class is discouraged.
class FatalStream
{
 public:
  FatalStream(const char* function, const char* file, int line);
  FatalStream() : d_abort(false) {}
  [[noreturn]] ~FatalStream();

  std::ostream& stream();

 private:
  void Flush();
  /** Whether to abort */
  bool d_abort;
};

// Helper class that changes the type of an std::ostream& into a void. See
// "Implementation notes" for more information.
class OstreamVoider
{
 public:
  OstreamVoider() {}
  // The operator precedence between operator& and operator<< is critical here.
  void operator&(std::ostream&) {}
};

// ALFC_FATAL() always aborts a function and provides a convenient way of
// formatting error messages. This can be used instead of a return type.
//
// Example function that returns a type Foo:
//   Foo bar(T t) {
//     switch(t.type()) {
//     ...
//     default:
//       ALFC_FATAL() << "Unknown T type " << t.enum();
//     }
//   }
#define ALFC_FATAL() \
  FatalStream().stream()

/* GCC <= 9.2 ignores ALFC_NO_RETURN of ~FatalStream() if
 * used in template classes (e.g., CDHashMap::save()).  As a workaround we
 * explicitly call abort() to let the compiler know that the
 * corresponding function call will not return. */
#define SuppressWrongNoReturnWarning abort()

// Define ALFC_PREDICT_FALSE// Define ALFC_PREDICT_FALSE(x) that helps the
// compiler predict that x will be false (if there is compiler support).
#ifdef __has_builtin
#if __has_builtin(__builtin_expect)
#define ALFC_PREDICT_FALSE(x) (__builtin_expect(x, false))
#define ALFC_PREDICT_TRUE(x) (__builtin_expect(x, true))
#else
#define ALFC_PREDICT_FALSE(x) x
#define ALFC_PREDICT_TRUE(x) x
#endif
#else
#define ALFC_PREDICT_FALSE(x) x
#define ALFC_PREDICT_TRUE(x) x
#endif

// If `cond` is true, log an error message and abort the process.
// Otherwise, does nothing. This leaves a hanging std::ostream& that can be
// inserted into.
#define ALFC_FATAL_IF(cond, function, file, line) \
  ALFC_PREDICT_FALSE(!(cond))                     \
  ? (void)0                                       \
  : alfc::OstreamVoider() & alfc::FatalStream(function, file, line).stream()

// If `cond` is false, log an error message and abort()'s the process.
// Otherwise, does nothing. This leaves a hanging std::ostream& that can be
// inserted into using operator<<. Example usages:
//   AlwaysAssert(x >= 0);
//   AlwaysAssert(x >= 0) << "x must be positive";
//   AlwaysAssert(x >= 0) << "expected a positive value. Got " << x << "
//   instead";
#define AlwaysAssert(cond)                                        \
  ALFC_FATAL_IF(!(cond), __PRETTY_FUNCTION__, __FILE__, __LINE__) \
      << "Check failure\n\n " << #cond << "\n"

// Assert is a variant of AlwaysAssert() that is only checked when
// ALFC_ASSERTIONS is defined. We rely on the optimizer to remove the deadcode.
#ifdef ALFC_ASSERTIONS
#define Assert(cond) AlwaysAssert(cond)
#else
#define Assert(cond) \
  ALFC_FATAL_IF(false, __PRETTY_FUNCTION__, __FILE__, __LINE__)
#endif

}  // namespace alfc

#endif /* ALFC__CHECK_H */
