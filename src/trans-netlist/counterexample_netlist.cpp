/*******************************************************************\

Module: Extracting Counterexamples

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <iostream>

#include <util/namespace.h>
#include <util/threeval.h>

#include <langapi/language_util.h>

#include "instantiate.h"
#include "counterexample_netlist.h"

/*******************************************************************\

Function: show_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_state(
  const propt &solver,
  const bmc_mapt &map,
  const namespacet &ns,
  unsigned timeframe)
{
  std::cout << "Transition system state " << timeframe << "\n";
  std::cout << "----------------------------------------------------\n";

  for(var_mapt::mapt::const_iterator
      it=map.var_map.map.begin();
      it!=map.var_map.map.end(); it++)
  {
    const var_mapt::vart &var=it->second;
    
    if(var.is_latch() || var.is_input() || var.is_wire())
    {
      std::cout << it->first << "=";

      std::string value;

      for(unsigned i=0; i<var.bits.size(); i++)
      {
        literalt l=map.get(timeframe, var.bits[i]);

        char ch;

        switch(solver.l_get(l).get_value())
        {
         case tvt::TV_TRUE: ch='1'; break;
         case tvt::TV_FALSE: ch='0'; break;
         default: ch='?'; break;
        }

        value=ch+value;
      }

      if(var.type.id()==ID_range ||
         var.type.id()==ID_unsignedbv ||
         var.type.id()==ID_signedbv)
      {
        exprt value_expr(ID_constant, var.type);

        if(var.type.id()==ID_range)
        {
          mp_integer i=binary2integer(value, false);
          mp_integer from=string2integer(var.type.get_string(ID_from));
          value_expr.set(ID_value, integer2string(i+from));
        }
        else
          value_expr.set(ID_value, value);

        std::cout << from_expr(ns, it->first, value_expr);
        std::cout << " (" << value << ")";
      }
      else
        std::cout << value;

      std::cout << '\n';
    }
  }

  std::cout << std::endl;
}

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
  
  forall_symbol_module_map(it, symbol_table.symbol_module_map, module)
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

  std::cout << std::endl;
}

/*******************************************************************\

Function: show_counterexample

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_counterexample(
  message_handlert &message_handler,
  const propt &solver,
  const bmc_mapt &map,
  const namespacet &ns,
  language_uit::uit ui)
{
  for(unsigned t=0; t<map.get_no_timeframes(); t++)
    show_state(solver, map, ns, t);
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

/*******************************************************************\

Function: show_counterexample

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_counterexample(
  const std::list<exprt> &properties,
  const std::list<bvt> &prop_bv,
  message_handlert &message_handler,
  const propt &solver,
  const bmc_mapt &map,
  const namespacet &ns,
  language_uit::uit ui)
{
  unsigned p=0;
  messaget message(message_handler);

  for(std::list<bvt>::const_iterator p_it=prop_bv.begin();
      p_it!=prop_bv.end();
      p_it++, p++)
  {
    const bvt &bv=*p_it;
    assert(bv.size()==map.get_no_timeframes());
  
    for(unsigned t=0; t<map.get_no_timeframes(); t++)
    {
      tvt result=solver.l_get(bv[t]);

      if(result.is_unknown())
      {
        message.warning() << "got unknown-valued property literal" 
                          << messaget::eom;
      }
      else if(result.is_false())
      {
        std::cout << "property "
                  << (p+1) 
                  << " violated in time frame " << t
                  << ":" << '\n' << '\n';

        for(unsigned x=0; x<=t; x++)
          show_state(solver, map, ns, x);

        std::cout << std::endl;
        break; // next property
      }
    }
  }
}
