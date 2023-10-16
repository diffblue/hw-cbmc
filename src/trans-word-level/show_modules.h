/*******************************************************************\

Module: Show Modules

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_SHOW_MODULES_H
#define CPROVER_TRANS_SHOW_MODULES_H

#include <util/symbol_table_base.h>

void show_modules(const symbol_table_baset &, std::ostream &);

void show_modules_xml(const symbol_table_baset &, std::ostream &);

#endif
