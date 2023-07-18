#include "input.h"

#include <fstream>
#include <iostream>

namespace atc {

/** File input class */
class FileInput : public Input
{
 public:
  FileInput(const std::string& filename) : Input()
  {
    d_fs.open(filename, std::fstream::in);
    if (!d_fs.is_open())
    {
      std::stringstream ss;
      ss << "Couldn't open file: " << filename;
      std::cerr << ss.str();
      exit(1);
    }
  }
  std::istream* getStream() override { return &d_fs; }

 private:
  /** File stream */
  std::ifstream d_fs;
};

Input::Input() {}

bool Input::isInteractive() const { return false; }

std::unique_ptr<Input> Input::mkFileInput(const std::string& filename)
{
  return std::unique_ptr<Input>(new FileInput(filename));
}

}  // namespace atc
