#ifndef FILEYSTEM_H
#define FILEYSTEM_H

#include <string>

namespace alfc {

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
  bool isAbsoluste() const;

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
  std::string rawPath;
};

bool operator<(const Filepath&, const Filepath&);
std::ostream& operator<<(std::ostream&, const Filepath&);

}  // namespace alfc

#endif /* FILESYSTEM_H */
