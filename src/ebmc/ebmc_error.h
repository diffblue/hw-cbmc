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

  std::optional<int> exit_code() const
  {
    return __exit_code;
  }

  ebmc_errort with_exit_code(int exit_code) &&
  {
    __exit_code = exit_code;
    return std::move(*this);
  }

  ebmc_errort with_location(source_locationt _location) &&
  {
    __location = std::move(_location);
    return std::move(*this);
  }

  const source_locationt &location() const
  {
    return __location;
  }

protected:
  std::ostringstream message;
  std::optional<int> __exit_code = {};
  source_locationt __location = source_locationt::nil();
};

/// add to the diagnostic information in the given ebmc_error exception
template <typename T>
ebmc_errort operator<<(ebmc_errort &&e, const T &message)
{
  e.message_ostream() << message;
  return std::move(e);
}

#endif // EBMC_ERROR_H
