/*******************************************************************\

Module: Unwinding the Properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_NETLIST_PROPERTY_NETLIST_H
#define CPROVER_TRANS_NETLIST_PROPERTY_NETLIST_H

#include <util/symbol_table.h>
#include <util/message.h>
#include <util/namespace.h>

#include <solvers/prop/prop.h>
#include <solvers/prop/prop_conv.h>

#include "bmc_map.h"

void property(
  const exprt &property_expr,
  bvt &prop_bv,
  message_handlert &,
  propt &solver,
  const bmc_mapt &map,
  const namespacet &);

#endif
