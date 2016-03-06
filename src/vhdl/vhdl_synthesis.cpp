/*******************************************************************\

Module: VHDL Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "vhdl_synthesis.h"
#include "vhdl_synthesis_class.h"

/*******************************************************************\

Function: vhdl_synthesist::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool vhdl_synthesist::operator()()
{
  try
  {
    
    return false;
  }
  catch(...)
  {
    return true;
  }
}

/*******************************************************************\

Function: vhdl_synthesis

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool vhdl_synthesis(
  symbol_tablet &symbol_table,
  const irep_idt &module,
  message_handlert &message_handler)
{
  return vhdl_synthesist(symbol_table, module, message_handler)();
}
