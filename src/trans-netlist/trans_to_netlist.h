/*******************************************************************\

Module: Transition System represented by a Netlist

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_NETLIST_TRANS_H
#define CPROVER_TRANS_NETLIST_TRANS_H

#include <util/expr.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/symbol_table_base.h>

void convert_trans_to_netlist(
  symbol_table_baset &,
  const irep_idt &module,
  const std::map<irep_idt, exprt> &properties,
  class netlistt &dest,
  message_handlert &);

#endif
