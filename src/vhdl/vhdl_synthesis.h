/*******************************************************************\

Module: VHDL Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VHDL_SYNTHESIS_H
#define CPROVER_VHDL_SYNTHESIS_H

#include <util/symbol_table.h>
#include <util/message.h>

bool vhdl_synthesis(
  symbol_tablet &,
  const irep_idt &module,
  message_handlert &);

#endif

