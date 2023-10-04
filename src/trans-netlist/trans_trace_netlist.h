/*******************************************************************\

Module: Extracting Counterexamples

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_TRACE_NETLIST_H
#define CPROVER_TRANS_TRACE_NETLIST_H

#include "bmc_map.h"
#include "trans_trace.h"

trans_tracet compute_trans_trace(
  const bvt &prop_bv,
  const bmc_mapt &,
  const class propt &solver,
  const namespacet &);

#endif
