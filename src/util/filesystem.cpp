#include "util/filesystem.h"

#include <fstream>
#include <sstream>
#include <vector>

#include "base/check.h"

namespace alfc {
Filepath::Filepath() {}

Filepath::Filepath(std::string rawPath)
{
  /* Trim the input path */
  size_t first = rawPath.find_first_not_of(' ');
  if (std::string::npos == first)
  {
    this->rawPath = rawPath;
    return;
  }
  size_t last = rawPath.find_last_not_of(' ');
  this->rawPath = rawPath.substr(first, (last - first + 1));
}

Filepath::Filepath(const char* rawPath)
{
  std::string path = std::string(rawPath);
  /* Trim the input path */
  size_t first = path.find_first_not_of(' ');
  if (std::string::npos == first)
  {
    this->rawPath = path;
    return;
  }
  size_t last = path.find_last_not_of(' ');
  this->rawPath = path.substr(first, (last - first + 1));
}

Filepath::~Filepath() {}

bool Filepath::isAbsoluste() const
{
#ifdef _WIN32
  static_assert(false, "File system support for Windows not implemented.");
#endif
  return rawPath[0] == '/';
}

bool Filepath::exists() const
{
  std::ifstream f;
  return f.good();
}

void Filepath::append(const Filepath path) { rawPath.append(path.rawPath); }

void Filepath::makeCanonical()
{
#ifdef _WIN32
  static_assert(false, "File system support for Windows not implemented.");
#endif

  if (rawPath.length() == 0)
  {
    return;
  }

  size_t start = 0;
  size_t parent_prefix_len = 0;
  bool is_absolute = false;

  std::vector<std::pair<size_t, size_t>> segments;
  while (true)
  {
    size_t next = rawPath.find('/', start);
    if (next >= rawPath.length())
    {
      // Done
      size_t len = rawPath.length() - start;
      segments.push_back(std::pair(start, len));
      break;
    }
    if (next == 0)
    {
      is_absolute = true;
      start = 1;
      continue;
    }
    size_t len = next - start;
    // Empty segment
    if (len == 0)
    {
      start = next + 1;
      continue;
    }
    // "current folder"
    if (rawPath.compare(start, len, ".") == 0)
    {
      start = next + 1;
      continue;
    }
    // "parent folder"
    if (rawPath.compare(start, len, "..") == 0)
    {
      start = next + 1;
      if (segments.empty())
      {
        parent_prefix_len += 1;
      }
      else
      {
        // Pop segment
        segments.pop_back();
      }
      continue;
    }
    segments.push_back(std::pair(start, len));
    start = next + 1;
  }

  std::stringstream newPath;
  bool first = true;

  if (is_absolute)
  {
    newPath << "/";
  }

  for (size_t i = 0; i < parent_prefix_len; i++)
  {
    newPath << "../";
  }

  for (auto it = segments.begin(); it != segments.end(); it++)
  {
    if (!first)
    {
      newPath << "/";
    }
    newPath << rawPath.substr(it->first, it->second);
    first = false;
  }
  rawPath = newPath.str();
}

Filepath Filepath::parentPath() const
{
#ifdef _WIN32
  static_assert(false, "File system support for Windows not implemented.");
#endif

  size_t last = this->rawPath.find_last_of("/");
  // If there are no folders, the parent is the empty string
  if (last == std::string::npos)
  {
    return Filepath("");
  }
  std::string newPath = this->rawPath.substr(0, last + 1);
  return Filepath(newPath);
}

std::string Filepath::getRawPath() const { return this->rawPath; }

bool operator<(const Filepath& a, const Filepath& b)
{
  return a.getRawPath() < b.getRawPath();
}

std::ostream& operator<<(std::ostream& os, const Filepath& obj)
{
  os << obj.getRawPath() << '\n';
  return os;
}
}  // namespace alfc
