/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "vhdl_typecheck.h"

bool vhdl_typecheck(
  vhdl_parse_treet &,
  symbol_tablet &symbol_table,
  const std::string &module,
  message_handlert &)
{
  symbolt symbol;
  
  symbol.name="vhdl::"+module;
  symbol.type=typet(ID_module);
  symbol.base_name=module;

  symbol_table.add(symbol);

  return false;
}

