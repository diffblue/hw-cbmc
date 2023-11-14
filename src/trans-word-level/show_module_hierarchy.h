/*******************************************************************\

Module: Show Module Hierarchy

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TRANS_WORD_LEVEL_SHOW_MODULE_HIERARCHY_H
#define CPROVER_TRANS_WORD_LEVEL_SHOW_MODULE_HIERARCHY_H

#include <util/symbol_table_base.h>

void show_module_hierarchy(
  const symbol_table_baset &,
  const symbolt &main_symbol,
  std::ostream &);

#endif
