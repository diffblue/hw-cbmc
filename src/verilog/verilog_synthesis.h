/*******************************************************************\

Module: Verilog Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_SYNTHESIS_H
#define CPROVER_VERILOG_SYNTHESIS_H

#include <util/message.h>
#include <util/options.h>
#include <util/symbol_table_base.h>

bool verilog_synthesis(
  symbol_table_baset &,
  const irep_idt &module,
  message_handlert &,
  const optionst &);

bool verilog_synthesis(
  exprt &,
  const irep_idt &module_identifier,
  message_handlert &,
  const namespacet &);

#endif
