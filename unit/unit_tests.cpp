/*******************************************************************\

Module: Unit Tests Main

Author: Daniel Kroening, Amazon, dkr@amazon.com

\*******************************************************************/

#define CATCH_CONFIG_MAIN
#include <util/irep.h>

#include <testing-utils/use_catch.h>

// Debug printer for irept
std::ostream &operator<<(std::ostream &os, const irept &value)
{
  os << value.pretty();
  return os;
}
