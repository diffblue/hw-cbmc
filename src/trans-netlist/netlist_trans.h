/*******************************************************************\

Module: Transition System represented by a Netlist

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_NETLIST_TRANS_H
#define CPROVER_TRANS_NETLIST_TRANS_H

#include <util/namespace.h>
#include <util/message.h>
#include <util/symbol_table.h>
#include <util/std_expr.h>

void convert_trans_to_netlist(
  symbol_tablet &symbol_table,
  const irep_idt &module,
  const std::list<exprt> &properties,
  class netlistt &dest,
  message_handlert &message_handler);

#endif
