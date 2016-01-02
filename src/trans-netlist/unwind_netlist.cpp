/*******************************************************************\

Module: Unwinding Netlists

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/i2string.h>

#include "unwind_netlist.h"

/*******************************************************************\

Function: unwind

  Inputs:

 Outputs:

 Purpose: Unwind timeframe by timeframe

\*******************************************************************/

void unwind(
  const netlistt &netlist,
  bmc_mapt &bmc_map,
  messaget &message,
  cnft &solver,
  bool add_initial_state,
  unsigned t)
{
  if(add_initial_state && t==0)
  {
    // do initial state
    message.status() << "Initial State" << messaget::eom;
    
    for(unsigned i=0; i<netlist.initial.size(); i++)
      solver.l_set_to(
        bmc_map.translate(0, netlist.initial[i]),
        true);
  }

  // do transitions
  bool last=(t==bmc_map.timeframe_map.size()-1);

  if(last)
    message.status() << "Transition " << t << messaget::eom;
  else
    message.status() << "Transition " << t << "->" << t+1 << messaget::eom;
  
  const bmc_mapt::timeframet &timeframe=bmc_map.timeframe_map[t];
  
  for(unsigned n=0; n<timeframe.size(); n++)
  {
    const aig_nodet &node=netlist.get_node(literalt(n, false));

    if(node.is_and() && timeframe[n].is_visible)
    {
      literalt la=bmc_map.translate(t, node.a);
      literalt lb=bmc_map.translate(t, node.b);
    
      solver.gate_and(la, lb, timeframe[n].solver_literal);
    }
  }

  // transition constraints
  for(unsigned i=0; i<netlist.transition.size(); i++)
    solver.l_set_to(
      bmc_map.translate(t, netlist.transition[i]),
      true);

  if(!last)
  {     
    // joining the latches between timeframe and timeframe+1
    for(var_mapt::mapt::const_iterator
        v_it=netlist.var_map.map.begin();
        v_it!=netlist.var_map.map.end();
        v_it++)
    {
      const var_mapt::vart &var=v_it->second;
      if(var.is_latch())
      {
        for(unsigned bit_nr=0; bit_nr<var.bits.size(); bit_nr++)
        {
          const var_mapt::vart::bitt &bit=var.bits[bit_nr];
          
          literalt l_from=bit.next;
          literalt l_to=bit.current;

          if(l_from.is_constant() ||
             bmc_map.timeframe_map[t][l_from.var_no()].is_visible)
            solver.set_equal(
              bmc_map.translate(t, l_from),
              bmc_map.translate(t+1, l_to));
        }
      }
    }
  }
}

/*******************************************************************\

Function: unwind

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void unwind(
  const netlistt &netlist,
  bmc_mapt &bmc_map,
  messaget &message,
  cnft &solver,
  bool add_initial_state)
{
  for(unsigned t=0; t<bmc_map.timeframe_map.size(); t++)
    unwind(netlist, bmc_map, message, solver, add_initial_state, t);
}

/*******************************************************************\

Function: unwind_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void unwind_property(
  const netlistt &netlist,
  const bmc_mapt &bmc_map,
  unsigned property_nr,
  bvt &prop_bv)
{
  prop_bv.resize(bmc_map.timeframe_map.size());

  for(unsigned t=0;
      t<bmc_map.timeframe_map.size();
      t++)
  {
    literalt l=bmc_map.translate(t, netlist.properties[property_nr]);
    prop_bv[t]=l;
  }
}
