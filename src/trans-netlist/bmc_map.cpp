/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <solvers/flattening/boolbv_width.h>

#include "bmc_map.h"

/*******************************************************************\

Function: bmc_mapt::map_timeframes

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmc_mapt::map_timeframes(
  const netlistt &netlist,
  unsigned no_timeframes,
  propt &solver)
{
  var_map=netlist.var_map;
  timeframe_map.resize(no_timeframes);
  
  for(unsigned t=0; t<timeframe_map.size(); t++)
  {
    timeframet &timeframe=timeframe_map[t];
    timeframe.resize(netlist.number_of_nodes());

    for(unsigned n=0; n<timeframe.size(); n++)
    {
      literalt solver_literal=solver.new_variable();
      timeframe[n].solver_literal=solver_literal;

      // keep a reverse map for variable nodes
      if(netlist.nodes[n].is_var())
      {
        reverse_entryt &e=reverse_map[solver_literal];
        e.timeframe=t;
        e.netlist_literal=literalt(n, false);
      }
    }
  }
}

