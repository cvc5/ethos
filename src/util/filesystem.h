#ifndef FILEYSTEM_H
#define FILEYSTEM_H

#include <string>

namespace alfc {
class Filepath
{
 public:
  Filepath();
  Filepath(std::string rawPath);
  Filepath(const char* rawPath);

  ~Filepath();

  bool isAbsoluste() const;
  bool exists() const;
  void append(const Filepath);
  void makeCanonical();
  Filepath parentPath() const;
  std::string getRawPath() const;

 private:
  std::string rawPath;
};

bool operator<(const Filepath&, const Filepath&);
std::ostream& operator<<(std::ostream&, const Filepath&);

}  // namespace alfc

#endif /* FILESYSTEM_H */
