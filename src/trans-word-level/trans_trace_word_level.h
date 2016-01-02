/*******************************************************************\

Module: Extracting Counterexamples

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_TRACE_WORD_LEVEL_H
#define CPROVER_TRANS_TRACE_WORD_LEVEL_H

#include "../trans-netlist/trans_trace.h"

// word-level without properties

void compute_trans_trace(
  const decision_proceduret &decision_procedure,
  unsigned no_timeframes,
  const namespacet &ns,
  const irep_idt &module,
  trans_tracet &dest);

// word-level with properties
  
void compute_trans_trace(
  const bvt &prop_bv,
  const class prop_convt &solver,
  unsigned no_timeframes,
  const namespacet &ns,
  const irep_idt &module,
  trans_tracet &dest);

#endif
