#include "parser.h"

#include <iostream>

using namespace atc;

int main( int argc, char* argv[] )
{
  if (argc!=2)
  {
    std::cerr << "Usage" << std::endl;
    exit(1);
  }
  State s;
  Parser p(s);
  p.setFileInput(argv[1]);
  bool parsedCommand;
  do
  {
    parsedCommand = p.parseNextCommand();
  }while (parsedCommand);
  std::cout << "success" << std::endl;
  return 0;
}
