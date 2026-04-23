/*******************************************************************\

Module: Flex Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "flex_interface.h"

#include <util/invariant.h>

#include <istream>

std::size_t flex_interfacet::yy_input(char *buffer, std::size_t max_size)
{
  PRECONDITION(in != nullptr);

  std::size_t result = 0;
  while(result < max_size)
  {
    char ch;
    if(!in->get(ch))
      break; // eof
    buffer[result++] = ch;
    if(ch == '\n')
    {
      // We need to abort prematurely to enable
      // switching input streams, e.g., for include files.
      break;
    }
  }
  return result;
}
