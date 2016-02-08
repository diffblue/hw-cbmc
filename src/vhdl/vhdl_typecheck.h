/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VHDL_TYPECHECK_H
#define CPROVER_VHDL_TYPECHECK_H

#include <util/symbol_table.h>
#include <util/message.h>

#include "vhdl_parse_tree.h"

bool vhdl_typecheck(
  const vhdl_parse_treet &,
  symbol_tablet &,
  const std::string &module,
  message_handlert &);

#endif

