/*******************************************************************\

Module: SMV Typechecking

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "smv_range.h"

#include <ostream>

std::ostream &operator<<(std::ostream &out, const smv_ranget &range)
{
  return out << range.from << ".." << range.to;
}
