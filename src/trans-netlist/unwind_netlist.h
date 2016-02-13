/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_UNWIND_NETLIST_GRAPH_H
#define CPROVER_TRANS_UNWIND_NETLIST_GRAPH_H

#include <cassert>

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

void unwind(
  const netlistt &netlist,
  bmc_mapt &bmc_map,
  messaget &message,
  cnft &solver,
  bool add_initial_state,
  unsigned timeframe);

void unwind_property(
  const exprt &property_expr,
  bvt &prop_bv,
  message_handlert &,
  propt &solver,
  const bmc_mapt &map,
  const namespacet &);

void unwind_property(
  const netlistt &netlist,
  const bmc_mapt &bmc_map,
  unsigned property_nr,
  bvt &prop_bv);

#endif
