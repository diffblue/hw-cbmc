/*******************************************************************\

Module: Transition System represented by a Netlist

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_NETLIST_TRANS_H
#define CPROVER_TRANS_NETLIST_TRANS_H

#include <namespace.h>
#include <message.h>
#include <symbol_table.h>
#include <std_expr.h>

void convert_trans_to_netlist(
  symbol_tablet &symbol_table,
  const irep_idt &module,
  const std::list<exprt> &properties,
  class netlistt &dest,
  messaget &message);

#endif
