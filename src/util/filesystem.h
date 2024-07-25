/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef FILEYSTEM_H
#define FILEYSTEM_H

#include <string>

// comment this to avoid issues in older versions of g++/C++
//#define USE_CPP_FILESYSTEM

#ifdef USE_CPP_FILESYSTEM
#include <filesystem>
#endif

namespace ethos {

/**
 * Simple handler for filepaths.  Only supports Unix-style paths for
 * now.  Does not use C++ 17 features.
 */
class Filepath
{
 public:
  Filepath();

  /**
   * @param rawPath A string of the filepath.
   */
  Filepath(std::string rawPath);

  /**
   * @param rawPath A C-style string of the filepath.
   */
  Filepath(const char* rawPath);

  ~Filepath();

  /**
   * @return `true` if the current path starts with '/'.
   */
  bool isAbsolute() const;

  /**
   * @return `true` the current path points to an existing file.
   */
  bool exists() const;

  /**
   * Appends a path to this path.  Does not do any normalization.
   * @param path is the path to append.
   */
  void append(const Filepath path);

  /**
   * This removes segments of the path that are superflous:
   *   - Repeated slashes: "//"
   *   - Parten folders, not at the start.  "foo/../bar" becomes
   *     "bar", but "../baz" is unchanged.
   *   - Curent folder segments. "foo/./bar" becomes "foo/bar".
   */
  void makeCanonical();

  /**
   * @return The current path, but with the filename cut off.
   */
  Filepath parentPath() const;

  /**
   * @return A copy of the underlying string.
   */
  std::string getRawPath() const;

 private:
#ifndef USE_CPP_FILESYSTEM
  std::string rawPath;
#else
  std::filesystem::path rawPath;
#endif
};

bool operator<(const Filepath&, const Filepath&);
std::ostream& operator<<(std::ostream&, const Filepath&);

}  // namespace ethos

#endif /* FILESYSTEM_H */
