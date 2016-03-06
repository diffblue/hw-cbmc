/*******************************************************************\

Module: Verilog Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_SYNTHESIS_H
#define CPROVER_VERILOG_SYNTHESIS_H

#include <util/symbol_table.h>
#include <util/message.h>
#include <util/options.h>

bool verilog_synthesis(
  symbol_tablet &symbol_table,
  const irep_idt &module,
  message_handlert &message_handler,
  const optionst &options);

#endif
