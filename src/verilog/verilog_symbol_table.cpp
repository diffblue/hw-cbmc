/*******************************************************************\

Module: Verilog Type Checker Base

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_symbol_table.h"

/*******************************************************************\

Function: verilog_symbol_tablet::symbol_table_lookup

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbolt &verilog_symbol_tablet::symbol_table_lookup(const irep_idt &identifier)
{
  auto it=symbol_table.get_writeable(identifier);

  if(it==nullptr)
    throw "symbol "+id2string(identifier)+" not found";

  return *it;
}
