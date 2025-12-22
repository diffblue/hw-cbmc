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
  const std::string &module_identifier,
  message_handlert &message_handler,
  bool do_spec = true);

/// returns the identifier for the module with given base name
irep_idt smv_module_symbol(const irep_idt &module_base_name);

/// returns the base_name for the module with given identifier
irep_idt smv_module_base_name(const irep_idt &module_identifier);

#endif
