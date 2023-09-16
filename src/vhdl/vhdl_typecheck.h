/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VHDL_TYPECHECK_H
#define CPROVER_VHDL_TYPECHECK_H

#include <util/message.h>
#include <util/symbol_table_base.h>

#include "vhdl_parse_tree.h"

bool vhdl_typecheck(
  const vhdl_parse_treet &,
  symbol_table_baset &,
  const std::string &module,
  message_handlert &);

#endif

