/*******************************************************************\

Module: Flex Interface

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "flex_interface.h"

#include <util/invariant_utils.h>

#include <istream>

std::size_t flex_interface_baset::yy_input(char *buffer, std::size_t max_size)
{
  PRECONDITION(in != nullptr);

  // Bulk read via the stream buffer, avoiding a per-character istream
  // sentry. This is safe because each tokenizer has its own (reentrant)
  // scanner, so we no longer need to stop at newlines to switch input
  // streams.
  auto count =
    in->rdbuf()->sgetn(buffer, static_cast<std::streamsize>(max_size));
  return count < 0 ? 0 : static_cast<std::size_t>(count);
}
