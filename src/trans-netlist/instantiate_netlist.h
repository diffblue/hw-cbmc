/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_NETLIST_INSTANTIATE_NETLIST_H
#define CPROVER_TRANS_NETLIST_INSTANTIATE_NETLIST_H

#include <util/expr.h>
#include <util/message.h>
#include <util/namespace.h>

#include "var_map.h"

// bit-level

void instantiate_constraint(
  propt &solver,
  const var_mapt &var_map,
  const exprt &expr,
  const namespacet &,
  message_handlert &);

literalt instantiate_convert(
  propt &solver,
  const var_mapt &var_map,
  const exprt &expr,
  const namespacet &,
  message_handlert &);
  
void instantiate_convert(
  propt &solver,
  const var_mapt &var_map,
  const exprt &expr,
  const namespacet &,
  message_handlert &,
  bvt &bv);

#endif // CPROVER_TRANS_NETLIST_INSTANTIATE_NETLIST_H
