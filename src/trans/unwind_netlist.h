/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_UNWIND_NETLIST_GRAPH_H
#define CPROVER_TRANS_UNWIND_NETLIST_GRAPH_H

#include <assert.h>

#include <message.h>
#include <solvers/sat/cnf.h>

#include "netlist.h"
#include "bmc_map.h"

void unwind(
  const netlistt &netlist,
  bmc_mapt &bmc_map,
  messaget &message,
  cnft &solver,
  bool add_initial_state=true);

void unwind(
  const netlistt &netlist,
  bmc_mapt &bmc_map,
  messaget &message,
  cnft &solver,
  bool add_initial_state,
  unsigned timeframe);

void unwind_property(
  const netlistt &netlist,
  const bmc_mapt &bmc_map,
  messaget &message,
  std::list<bvt> &prop_bv,
  cnft &solver);

#endif
