/*******************************************************************\

Module: Verilog Type Checker Base

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_context.h"

/*******************************************************************\

Function: verilog_contextt::context_lookup

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbolt &verilog_contextt::context_lookup(const irep_idt &identifier)
{
  contextt::symbolst::iterator it=context.symbols.find(identifier);

  if(it==context.symbols.end())
    throw "symbol "+id2string(identifier)+" not found";

  return it->second;
}
