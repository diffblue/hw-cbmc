/*******************************************************************\

Module: Transition System represented by a Netlist

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_NETLIST_TRANS_H
#define CPROVER_TRANS_NETLIST_TRANS_H

#include <util/namespace.h>
#include <util/message.h>
#include <util/symbol_table.h>
#include <util/expr.h>

void convert_trans_to_netlist(
  symbol_tablet &symbol_table,
  const irep_idt &module,
  class netlistt &dest,
  message_handlert &message_handler);

#endif
