/*******************************************************************\

Module: Verilog Transition Relation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_VERILOG_TRANSITION_RELATION_H
#define CPROVER_VERILOG_VERILOG_TRANSITION_RELATION_H

#include <util/irep.h>

#include "verilog_standard.h"

class message_handlert;
class symbol_table_baset;
class transt;

/// Creates the transition relation for the given module from its
/// register-transfer level (RTL) representation. The module symbol's
/// value is set to the resulting trans expression, and the values of
/// the property symbols are set to the property conditions.
/// Throws ebmc_errort on failure.
transt verilog_transition_relation(
  symbol_table_baset &,
  const irep_idt &module_identifier,
  verilog_standardt,
  bool ignore_initial,
  bool initial_zero,
  message_handlert &);

#endif // CPROVER_VERILOG_VERILOG_TRANSITION_RELATION_H
