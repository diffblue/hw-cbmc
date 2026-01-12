/*******************************************************************\

Module: Transition System represented by a Netlist

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TRANS_NETLIST_TRANS_TO_NETLIST_SIMPLE_H
#define CPROVER_TRANS_NETLIST_TRANS_TO_NETLIST_SIMPLE_H

#include <util/expr.h>
#include <util/mathematical_expr.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/symbol_table_base.h>

void convert_trans_to_netlist_simple(
  symbol_table_baset &,
  const irep_idt &module,
  const transt &,
  const std::map<irep_idt, exprt> &properties,
  class netlistt &dest,
  message_handlert &);

#endif // CPROVER_TRANS_NETLIST_TRANS_TO_NETLIST_SIMPLE_H
