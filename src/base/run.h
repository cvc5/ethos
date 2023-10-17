#ifndef RUN_H
#define RUN_H

#include <string>
#include <ostream>

namespace alfc {

/**
 * Used for oracle calls.
 *
 * Run the call to command `call`, where `content` is passed as input.
 * Write the response on the `response` output stream.
 * Returns the exit status of the call.
 */
int run(const std::string& call,
      const std::string& content,
      std::ostream& response);

int runFile(const std::string& call, std::ostream& response);

}  // namespace alfc

#endif
