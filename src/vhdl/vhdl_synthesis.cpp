/*******************************************************************\

Module: VHDL Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>

#include "vhdl_synthesis.h"
#include "vhdl_synthesis_class.h"

/*******************************************************************\

Function: vhdl_synthesist::synth_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_synthesist::synth_code(const codet &code)
{
  const irep_idt &statement=code.get_statement();
  
  if(statement==ID_assign)
  {
  }
  else if(statement==ID_continuous_assign)
  {
  }
  else if(statement==ID_assert)
  {
  }
  else
  {
    error() << "unexpected statement during synthesis: "
            << statement << eom;
    throw 0;
  }
}

/*******************************************************************\

Function: vhdl_synthesist::synth_module

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_synthesist::synth_module(const exprt &module)
{
  for(auto & op : module.operands())
  {
    if(op.id()==ID_process)
      synth_process(op);
    else
    {
      error() << "unexpected module item during synthesis: "
              << op.id() << eom;
      throw 0;
    }
  }
}

/*******************************************************************\

Function: vhdl_synthesist::synth_process

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_synthesist::synth_process(const exprt &process)
{
  for(auto & op : process.operands())
    synth_code(to_code(op));
}

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
    symbol_tablet::symbolst::iterator s_it=
      symbol_table.symbols.find(module);

    if(s_it==symbol_table.symbols.end())
    {
      error() << "module `" << module << "' not found" << eom;
      throw 0;
    }
    
    symbolt &symbol=s_it->second;
    
    synth_module(symbol.value);
    
    transt trans_expr;

    trans_expr.invar()=conjunction(invar);
    trans_expr.init()=conjunction(init);
    trans_expr.trans()=conjunction(trans);
    
    symbol.value=trans_expr;
    
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
