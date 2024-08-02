/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Mathias Preiner, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************
 *
 * Output utility classes and functions.
 */

#ifndef EO__OUTPUT_H
#define EO__OUTPUT_H

#include <algorithm>
#include <cstdio>
#include <ios>
#include <iostream>
#include <set>
#include <string>
#include <utility>
#include <vector>

namespace ethos {

template <class T, class U>
std::ostream& operator<<(std::ostream& out, const std::pair<T, U>& p)
{
  return out << "[" << p.first << "," << p.second << "]";
}

template <class T>
std::ostream& operator<<(std::ostream& out, const std::vector<T>& children)
{
  out << "[";
  bool firstTime = true;
  for (const T& e : children)
  {
    if (firstTime)
    {
      firstTime = false;
    }
    else
    {
      out << ", ";
    }
    out << e;
  }
  out << "]";
  return out;
}

/**
 * A utility class to provide (essentially) a "/dev/null" streambuf.
 * If debugging support is compiled in, but debugging for
 * e.g. "parser" is off, then Trace("parser") returns a stream
 * attached to a null_streambuf instance so that output is directed to
 * the bit bucket.
 */
class null_streambuf : public std::streambuf
{
 public:
  /* Overriding overflow() just ensures that EOF isn't returned on the
   * stream.  Perhaps this is not so critical, but recommended; this
   * way the output stream looks like it's functioning, in a non-error
   * state. */
  int overflow(int c) override { return c; }
}; /* class null_streambuf */

/** A null stream-buffer singleton */
extern null_streambuf null_sb;
/** A null output stream singleton */
extern std::ostream null_os;

class Ethosostream
{
  static const std::string s_tab;
  static const int s_indentIosIndex;

  /** The underlying ostream */
  std::ostream* d_os;
  /** Are we in the first column? */
  bool d_firstColumn;

  /** The endl manipulator (why do we need to keep this?) */
  std::ostream& (*const d_endl)(std::ostream&);

  // do not allow use
  Ethosostream& operator=(const Ethosostream&);

 public:
  Ethosostream() : d_os(NULL), d_firstColumn(false), d_endl(&std::endl) {}
  explicit Ethosostream(std::ostream* os)
      : d_os(os), d_firstColumn(true), d_endl(&std::endl)
  {
  }

  Ethosostream& flush()
  {
    if (d_os != NULL)
    {
      d_os->flush();
    }
    return *this;
  }

  bool isConnected() const { return d_os != NULL; }
  operator std::ostream&() const { return isConnected() ? *d_os : null_os; }

  std::ostream* getStreamPointer() const { return d_os; }

  template <class T>
  Ethosostream& operator<<(T const& t)
  {
    if (d_os != nullptr)
    {
      if (d_firstColumn)
      {
        d_firstColumn = false;
        long indent = d_os->iword(s_indentIosIndex);
        for (long i = 0; i < indent; ++i)
        {
          d_os = &(*d_os << s_tab);
        }
      }
      *d_os << t;
    }
    return *this;
  }

  // support manipulators, endl, etc..
  Ethosostream& operator<<(std::ostream& (*pf)(std::ostream&))
  {
    if (d_os != NULL)
    {
      d_os = &(*d_os << pf);

      if (pf == d_endl)
      {
        d_firstColumn = true;
      }
    }
    return *this;
  }
  Ethosostream& operator<<(std::ios& (*pf)(std::ios&))
  {
    if (d_os != NULL)
    {
      d_os = &(*d_os << pf);
    }
    return *this;
  }
  Ethosostream& operator<<(std::ios_base& (*pf)(std::ios_base&))
  {
    if (d_os != NULL)
    {
      d_os = &(*d_os << pf);
    }
    return *this;
  }
  Ethosostream& operator<<(Ethosostream& (*pf)(Ethosostream&))
  {
    return pf(*this);
  }
}; /* class Ethosostream */

/**
 * Does nothing; designed for compilation of non-debug/non-trace
 * builds.  None of these should ever be called in such builds, but we
 * offer this to the compiler so it doesn't complain.
 */
class NullC
{
 public:
  operator bool() const { return false; }
  operator Ethosostream() const { return Ethosostream(); }
  operator std::ostream&() const { return null_os; }
}; /* class NullC */

extern NullC nullStream;

/** The warning output class */
class WarningC
{
  std::set<std::pair<std::string, size_t> > d_alreadyWarned;
  std::ostream* d_os;

 public:
  explicit WarningC(std::ostream* os) : d_os(os) {}

  Ethosostream operator()() const { return Ethosostream(d_os); }

  std::ostream& setStream(std::ostream* os)
  {
    d_os = os;
    return *d_os;
  }
  std::ostream& getStream() const { return *d_os; }
  std::ostream* getStreamPointer() const { return d_os; }

  bool isOn() const { return d_os != &null_os; }

  // This function supports the WarningOnce() macro, which allows you
  // to easily indicate that a warning should be emitted, but only
  // once for a given run of ethos.
  bool warnOnce(const std::string& file, size_t line)
  {
    std::pair<std::string, size_t> pr = std::make_pair(file, line);
    if (d_alreadyWarned.find(pr) != d_alreadyWarned.end())
    {
      // signal caller not to warn again
      return false;
    }

    // okay warn this time, but don't do it again
    d_alreadyWarned.insert(pr);
    return true;
  }

}; /* class WarningC */

/** The trace output class */
class TraceC
{
  std::ostream* d_os;
  std::vector<std::string> d_tags;

 public:
  explicit TraceC(std::ostream* os) : d_os(os) {}

  Ethosostream operator()() const { return Ethosostream(d_os); }
  Ethosostream operator()(const std::string& tag) const
  {
    if (isOn(tag))
    {
      return Ethosostream(d_os);
    }
    else
    {
      return Ethosostream();
    }
  }

  bool on(const std::string& tag)
  {
    d_tags.emplace_back(tag);
    return true;
  }
  bool off(const std::string& tag)
  {
    auto it = std::find(d_tags.begin(), d_tags.end(), tag);
    if (it != d_tags.end())
    {
      *it = d_tags.back();
      d_tags.pop_back();
    }
    return false;
  }

  bool isOn(const std::string& tag) const
  {
    // This is faster than using std::set::find() or sorting the vector and
    // using std::lower_bound.
    return !d_tags.empty()
           && std::find(d_tags.begin(), d_tags.end(), tag) != d_tags.end();
  }

  std::ostream& setStream(std::ostream* os)
  {
    d_os = os;
    return *d_os;
  }
  std::ostream& getStream() const { return *d_os; }
  std::ostream* getStreamPointer() const { return d_os; }

}; /* class TraceC */

/** The warning output singleton */
extern WarningC WarningChannel;
/** The trace output singleton */
extern TraceC TraceChannel;

#define Warning \
  (!ethos::WarningChannel.isOn()) ? ethos::nullStream : ethos::WarningChannel
#define WarningOnce                                       \
  (!ethos::WarningChannel.isOn()                           \
   || !ethos::WarningChannel.warnOnce(__FILE__, __LINE__)) \
      ? ethos::nullStream                                  \
      : ethos::WarningChannel
#ifdef EO_TRACING
#define TraceIsOn ethos::TraceChannel.isOn
#define Trace(tag) \
  !ethos::TraceChannel.isOn(tag) ? ethos::nullStream : ethos::TraceChannel()
#else /* EO_TRACING */
#define TraceIsOn ethos::__ethos_true() ? false : ethos::TraceChannel.isOn
#define Trace(tag) ethos::__ethos_true() ? ethos::nullStream : ethos::TraceChannel()
#endif /* EO_TRACING */

// Disallow e.g. !Trace("foo").isOn() forms
// because the ! will apply before the ? .
// If a compiler error has directed you here,
// just parenthesize it e.g. !(Trace("foo").isOn())
class __ethos_true
{
  [[maybe_unused]] void operator!();
  [[maybe_unused]] void operator~();
  [[maybe_unused]] void operator-();
  [[maybe_unused]] void operator+();

 public:
  inline operator bool() { return true; }
}; /* __ethos_true */

}  // namespace ethos

#endif /* EO__OUTPUT_H */
