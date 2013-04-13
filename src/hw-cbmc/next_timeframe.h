/*******************************************************************\

Module: The next_timeframe() statement

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <set>

#include <util/namespace.h>

void add_next_timeframe(
  symbolt &symbol,
  const irep_idt &struct_identifier,
  const std::set<irep_idt> &top_level_inputs,
  const namespacet &ns);
