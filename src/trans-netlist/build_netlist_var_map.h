/*******************************************************************\

Module: var_map for Netlist

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TRANS_NETLIST_BUILD_NETLIST_VAR_MAP_H
#define CPROVER_TRANS_NETLIST_BUILD_NETLIST_VAR_MAP_H

#include <util/symbol_table_base.h>

#include "var_map.h"

var_mapt build_netlist_var_map(symbol_table_baset &, const irep_idt &module);

#endif
