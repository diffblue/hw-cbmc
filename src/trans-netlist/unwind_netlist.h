/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_UNWIND_NETLIST_GRAPH_H
#define CPROVER_TRANS_UNWIND_NETLIST_GRAPH_H

#include <util/message.h>

#include <solvers/sat/cnf.h>

#include "bmc_map.h"
#include "netlist.h"

struct unwind_optionst
{
  /// assert the initial-state constraint at timeframe 0
  bool add_initial_state = true;
  /// assert the in-state AIG constraints (netlist.constraints)
  bool add_constraints = true;
};

void unwind(
  const netlistt &netlist,
  const bmc_mapt &bmc_map,
  messaget &message,
  cnft &solver,
  unwind_optionst options = {});

// unwind timeframes individually
void unwind(
  const netlistt &netlist,
  const bmc_mapt &bmc_map,
  messaget &message,
  cnft &solver,
  unwind_optionst options,
  std::size_t timeframe);

// Is the property supported?
bool netlist_bmc_supports_property(const class exprt &);

// unwind a netlist property
bvt unwind_property(const exprt &, const bmc_mapt &);

#endif
