/*******************************************************************\

Module: Verilog Preprocessor Error Class

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef VERILOG_PREPROCESSOR_ERROR_H
#define VERILOG_PREPROCESSOR_ERROR_H

#include <sstream>
#include <string>

class verilog_preprocessor_errort
{
public:
  verilog_preprocessor_errort() = default;
  verilog_preprocessor_errort(verilog_preprocessor_errort &&) = default;
  verilog_preprocessor_errort(const verilog_preprocessor_errort &other)
  {
    // ostringstream does not have a copy constructor
    message << other.message.str();
  }

  std::string what() const
  {
    return message.str();
  }

  std::ostringstream &message_ostream()
  {
    return message;
  }

protected:
  std::ostringstream message;
};

/// add to the diagnostic information in the given verilog_preprocessor_error exception
template <typename T>
verilog_preprocessor_errort
operator<<(verilog_preprocessor_errort &&e, const T &message)
{
  e.message_ostream() << message;
  return std::move(e);
}

#endif // VERILOG_PREPROCESSOR_ERROR_H
