/*******************************************************************\

Module: The set_inputs() statement

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <set>

#include <namespace.h>

void add_set_inputs(
  symbolt &symbol,
  const irep_idt &struct_identifier,
  const std::set<irep_idt> &top_level_inputs,
  const namespacet &ns);
