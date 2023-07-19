#ifndef ERROR_H
#define ERROR_H

#include <iostream>

namespace atc {

class Error
{
 public:
  static void reportError(const std::string& msg)
  {
    std::cerr << "ERROR: " << msg;
    exit(1);
  }
  static void reportWarning(const std::string& msg)
  {
    std::cerr << "WARNING: " << msg;
  }
};

}  // namespace atc

#endif 
