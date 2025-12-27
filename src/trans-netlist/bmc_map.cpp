/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <solvers/flattening/boolbv_width.h>

#include "bmc_map.h"

/*******************************************************************\

Function: bmc_mapt::bmc_mapt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bmc_mapt::bmc_mapt(
  const netlistt &netlist,
  std::size_t no_timeframes,
  propt &solver)
  : var_map(netlist.var_map)
{
  timeframe_map.resize(no_timeframes);

  for(std::size_t t = 0; t < timeframe_map.size(); t++)
  {
    timeframet &timeframe=timeframe_map[t];
    timeframe.resize(netlist.number_of_nodes());

    for(std::size_t n = 0; n < timeframe.size(); n++)
    {
      literalt solver_literal=solver.new_variable();
      timeframe[n].solver_literal = solver_literal;
    }
  }
}
