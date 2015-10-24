/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BMC_INSTANTIATE_NETLIST_H
#define CPROVER_BMC_INSTANTIATE_NETLIST_H

#include <util/hash_cont.h>
#include <util/expr.h>
#include <util/namespace.h>
#include <util/message.h>

#include <solvers/flattening/boolbv.h>

#include "bmc_map.h"

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

void instantiate_constraint(
  propt &solver,
  const bmc_mapt &bmc_map,
  const exprt &expr,
  unsigned current, unsigned next,
  const namespacet &,
  message_handlert &);

literalt instantiate_convert(
  propt &solver,
  const bmc_mapt &bmc_map,
  const exprt &expr,
  unsigned current, unsigned next,
  const namespacet &,
  message_handlert &);
  
void instantiate_convert(
  propt &solver,
  const bmc_mapt &bmc_map,
  const exprt &expr,
  unsigned current, unsigned next,
  const namespacet &,
  message_handlert &,
  bvt &bv);

#endif
