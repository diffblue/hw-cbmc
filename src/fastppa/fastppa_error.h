/*******************************************************************\

Module: FastPPA Error Class

Author: Kiro

\*******************************************************************/

#ifndef CPROVER_FASTPPA_FASTPPA_ERROR_H
#define CPROVER_FASTPPA_FASTPPA_ERROR_H

#include <sstream>
#include <string>

class fastppa_errort
{
public:
  fastppa_errort() = default;
  fastppa_errort(const fastppa_errort &other)
  {
    message << other.message.str();
  }
  fastppa_errort(fastppa_errort &&) = default;

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

template <typename T>
fastppa_errort operator<<(fastppa_errort &&e, const T &message)
{
  e.message_ostream() << message;
  return std::move(e);
}

#endif // CPROVER_FASTPPA_FASTPPA_ERROR_H
