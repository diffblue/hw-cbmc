/*******************************************************************\

Module: SMV Typechecking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SMV_TYPECHECK_H
#define CPROVER_SMV_TYPECHECK_H

#include <util/message.h>
#include <util/symbol_table_base.h>

#include "smv_parse_tree.h"

bool smv_typecheck(
  smv_parse_treet &smv_parse_tree,
  symbol_table_baset &,
  const std::string &module,
  message_handlert &message_handler,
  bool do_spec = true);

std::string smv_module_symbol(const std::string &module);

#endif
