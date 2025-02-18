/*******************************************************************\

Module: Verilog Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_SYNTHESIS_H
#define CPROVER_VERILOG_SYNTHESIS_H

#include <util/message.h>
#include <util/options.h>
#include <util/symbol_table_base.h>

#include "verilog_standard.h"

bool verilog_synthesis(
  symbol_table_baset &,
  const irep_idt &module,
  verilog_standardt,
  bool ignore_initial,
  message_handlert &);

bool verilog_synthesis(
  exprt &,
  const irep_idt &module_identifier,
  verilog_standardt,
  message_handlert &,
  const namespacet &);

#endif
