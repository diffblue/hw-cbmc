/*******************************************************************\

Module: Verilog Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_CONTEXT_H
#define CPROVER_VERILOG_CONTEXT_H

#include <util/symbol_table_base.h>

/*******************************************************************\

   Class: verilog_symbol_tablet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class verilog_symbol_tablet
{
public:
  verilog_symbol_tablet(symbol_table_baset &_symbol_table)
    : symbol_table(_symbol_table)
  {
  }

protected:
  symbol_table_baset &symbol_table;
  symbolt &symbol_table_lookup(const irep_idt &identifier);
};

#endif
