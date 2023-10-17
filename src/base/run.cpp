#include "base/run.h"

#include <fcntl.h>
#include <sched.h>
#include <sys/wait.h>
#include <unistd.h>

#include <cstdint>
#include <cstdlib>
#include <cwchar>
#include <type_traits>
#include <iostream>

namespace alfc {

int run(const std::string& call,
        const std::string& content,
        std::ostream& response)
{
  int read_pipe[2];
  int write_pipe[2];
  pipe(read_pipe);
  pipe(write_pipe);

  pid_t pid = fork();
  if (pid == -1)
  {
    // Forking failed.
    return -1;
  }
  if (pid == 0)
  {
    // We are the fork
    // Close parent ends of the pipe
    close(write_pipe[1]);
    close(read_pipe[0]);

    // Wire our ends of the pipe to stdin/out
    dup2(write_pipe[0], STDIN_FILENO);
    close(write_pipe[0]);
    dup2(read_pipe[1], STDOUT_FILENO);
    close(read_pipe[1]);

    const char* argv[] = {call.c_str(), NULL};
    execv(call.c_str(), (char**)argv);
    _exit(-1);  // This point is only reached if there is an error
  }
  else
  {
    // We are the parent
    // Close child ends of the pipe
    close(write_pipe[0]);
    close(read_pipe[1]);

    write(write_pipe[1], content.c_str(), content.length() + 1);
    // Wait for child and get return code
    int status;
    pid_t ret;
    bool error = false;
    while ((ret = waitpid(pid, &status, 0)) == -1)
    {
      if (errno != EINTR)
      {
        error = true;
        break;
      }
    }
    if ((ret == 0) || error || !(WIFEXITED(status) && !WEXITSTATUS(status)))
    {
      close(write_pipe[1]);
      close(read_pipe[0]);
      return -1;
    }

    char buffer[255];
    size_t num;
    // Do not block if pipe is not empty.
    fcntl(read_pipe[0], F_SETFL, O_NONBLOCK);
    while ((num = read(read_pipe[0], buffer, 255)) == 255)
    {
      response << buffer;
    }
    // Write partial buffer.
    response.write(buffer, num);

    close(write_pipe[1]);
    close(read_pipe[0]);
    return WEXITSTATUS(status);
  }
  return -1;
}

int runFile(const std::string& call, std::ostream& response)
{
  FILE* stream = popen(call.c_str(), "r");
  if (stream != nullptr)
  {
    int ch;
    while ((ch = fgetc(stream)) != EOF)
    {
      response << (unsigned char)ch;
    }
    return pclose(stream);
  }
  return -1;
}

}  // namespace alfc

