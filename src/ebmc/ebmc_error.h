/*******************************************************************\

Module: EBMC Error Class

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef EBMC_ERROR_H
#define EBMC_ERROR_H

#include <sstream>
#include <string>

class ebmc_errort
{
public:
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

/// add to the diagnostic information in the given ebmc_error exception
template <typename T>
ebmc_errort operator<<(ebmc_errort &&e, const T &message)
{
  e.message_ostream() << message;
  return std::move(e);
}

#endif // EBMC_ERROR_H
