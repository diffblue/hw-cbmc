/*******************************************************************\

Module: Elaboration of Verilog Compilation Units

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_ELABORATE_COMPILATION_UNIT_H
#define CPROVER_VERILOG_ELABORATE_COMPILATION_UNIT_H

#include <util/message.h>
#include <util/symbol_table_base.h>

#include "verilog_parse_tree.h"

/// throws ebmc_errort on failure
void verilog_elaborate_compilation_unit(
  const verilog_parse_treet &,
  symbol_table_baset &,
  message_handlert &);

#endif // CPROVER_VERILOG_ELABORATE_UNIT_H
