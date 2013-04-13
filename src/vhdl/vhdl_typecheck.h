/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VHDL_TYPECHECK_H
#define CPROVER_VHDL_TYPECHECK_H

#include <util/symbol_table.h>

bool convert_vhdl(void *root, symbol_tablet &symbol_table, std::string &error);

#endif

