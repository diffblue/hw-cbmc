/*******************************************************************\

Module: Extracting Counterexamples

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_TRACE_NETLIST_H
#define CPROVER_TRANS_TRACE_NETLIST_H

#include "bmc_map.h"
#include "trans_trace.h"

void compute_trans_trace(
  const bvt &prop_bv,
  const bmc_mapt &bmc_map,
  const class propt &solver,
  const namespacet &ns,
  trans_tracet &dest);

#endif
