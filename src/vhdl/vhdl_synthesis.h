/*******************************************************************\

Module: VHDL Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VHDL_SYNTHESIS_H
#define CPROVER_VHDL_SYNTHESIS_H

#include <util/message.h>
#include <util/symbol_table_base.h>

bool vhdl_synthesis(
  symbol_table_baset &,
  const irep_idt &module,
  message_handlert &);

#endif

