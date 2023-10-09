/*******************************************************************\

Module: Extracting Counterexamples

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_TRACE_WORD_LEVEL_H
#define CPROVER_TRANS_TRACE_WORD_LEVEL_H

#include <solvers/decision_procedure.h>

#include "../trans-netlist/trans_trace.h"

// word-level without properties

trans_tracet compute_trans_trace(
  const decision_proceduret &,
  std::size_t no_timeframes,
  const namespacet &,
  const irep_idt &module);

// word-level with properties

trans_tracet compute_trans_trace(
  const exprt::operandst &prop_handles,
  const decision_proceduret &solver,
  std::size_t no_timeframes,
  const namespacet &ns,
  const irep_idt &module);

#endif
