/*******************************************************************\

Module: Extracting Counterexamples

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <iostream>

#include <langapi/language_util.h>

#include "instantiate_word_level.h"
#include "counterexample_word_level.h"

/*******************************************************************\

Function: show_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_state(
  const decision_proceduret &solver,
  const namespacet &ns,
  const std::string &module,
  unsigned timeframe)
{
  std::cout << "Transition system state " << timeframe << "\n";
  std::cout << "----------------------------------------------------\n";

  const symbol_tablet &symbol_table=ns.get_symbol_table();
  
  for(auto it=symbol_table.symbol_module_map.lower_bound(module);
      it!=symbol_table.symbol_module_map.upper_bound(module);
      it++)
  {
    const symbolt &symbol=ns.lookup(it->second);

    if(!symbol.is_type)
    {
      exprt symbol_expr(ID_symbol, symbol.type);
      symbol_expr.set(ID_identifier, timeframe_identifier(timeframe, symbol.name));

      exprt value_expr=solver.get(symbol_expr);

      if(value_expr.is_not_nil())
      {
        std::cout << symbol.display_name() << "=";      
        std::cout << from_expr(ns, symbol.name, value_expr);
        std::cout << '\n';
      }
    }
  }

  std::cout << '\n' << std::flush;
}

/*******************************************************************\

Function: show_counterexample

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_counterexample(
  message_handlert &message_handler,
  const decision_proceduret &solver,
  unsigned no_timeframes,
  const namespacet &ns,
  const std::string &module,
  language_uit::uit ui)
{
  for(unsigned t=0; t<no_timeframes; t++)
    show_state(solver, ns, module, t);
}

