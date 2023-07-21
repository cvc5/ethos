#ifndef ERROR_H
#define ERROR_H

#include <iostream>

namespace alfc {

class ExprValue;

class Error
{
 public:
  static void reportError(const std::string& msg)
  {
    std::cerr << "ERROR: " << msg << std::endl;
    exit(1);
  }
  static void reportWarning(const std::string& msg)
  {
    std::cerr << "WARNING: " << msg << std::endl;
  }
};

}  // namespace alfc

#endif 
