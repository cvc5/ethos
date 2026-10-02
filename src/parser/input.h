/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef INPUT_H
#define INPUT_H

#include <memory>
#include <sstream>
#include <string>

namespace ethos {

/**
 * Wrapper to setup the necessary information for constructing a Lexer.
 *
 * Currently this is std::istream& obtainable via getStream.
 */
class Input
{
 public:
  Input();
  virtual ~Input() {}
  /** Set the input for the given file.
   *
   * @param filename the input filename
   */
  static std::unique_ptr<Input> mkFileInput(const std::string& filename);
  /** Set the input for the given stream.
   *
   * @param input the input
   */
  static std::unique_ptr<Input> mkStreamInput(std::istream& input);
  /** Set the input for the given string.
   *
   * @param input the input
   */
  static std::unique_ptr<Input> mkStringInput(const std::string& input);
  /** Get the stream to pass to the lexer. */
  virtual std::istream* getStream() = 0;
  /**
   * Is the stream of this input an interactive input? If so, we will read
   * it character-by-character.
   */
  virtual bool isInteractive() const;
};

}  // namespace cvc5

#endif /* CVC5__PARSER__SMT2_H */
