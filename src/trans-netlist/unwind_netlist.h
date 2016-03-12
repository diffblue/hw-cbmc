/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_UNWIND_NETLIST_GRAPH_H
#define CPROVER_TRANS_UNWIND_NETLIST_GRAPH_H

#include <util/message.h>
#include <util/namespace.h>

#include <solvers/sat/cnf.h>

#include "netlist.h"
#include "bmc_map.h"

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
  unsigned timeframe);

// unwind a property that has not yet been converted
void unwind_property(
  const exprt &property_expr,
  bvt &prop_bv,
  message_handlert &,
  propt &solver,
  const bmc_mapt &,
  const namespacet &);

// unwind a property that is given as netlist node
void unwind_property(
  const bmc_mapt &,
  literalt property_node,
  bvt &prop_bv);

#endif
