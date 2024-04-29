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

void unwind(
  const netlistt &netlist,
  bmc_mapt &bmc_map,
  messaget &message,
  cnft &solver,
  bool add_initial_state=true);

// unwind timeframes individually
void unwind(
  const netlistt &netlist,
  bmc_mapt &bmc_map,
  messaget &message,
  cnft &solver,
  bool add_initial_state,
  std::size_t timeframe);

// Is the property supported?
bool netlist_bmc_supports_property(const class exprt &);

// unwind a netlist property
void unwind_property(
  const netlistt::propertyt &,
  const bmc_mapt &,
  bvt &prop_bv);

#endif
