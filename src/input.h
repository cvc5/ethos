#ifndef INPUT_H
#define INPUT_H

#include <memory>
#include <sstream>
#include <string>

namespace alfc {

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
  /** Set the input for the given string.
   *
   * @param filename the input
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
