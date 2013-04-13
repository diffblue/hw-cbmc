/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BMC_INSTANTIATE_H
#define CPROVER_BMC_INSTANTIATE_H

#include <util/hash_cont.h>
#include <util/expr.h>
#include <util/namespace.h>
#include <util/message.h>

#include <solvers/flattening/boolbv.h>

#include "bmc_map.h"

void instantiate_constraint(
  propt &solver,
  const var_mapt &var_map,
  const exprt &expr,
  const namespacet &ns,
  messaget &message);

literalt instantiate_convert(
  propt &solver,
  const var_mapt &var_map,
  const exprt &expr,
  const namespacet &ns,
  messaget &message);
  
void instantiate_convert(
  propt &solver,
  const var_mapt &var_map,
  const exprt &expr,
  const namespacet &ns,
  messaget &message,
  bvt &bv);

void instantiate_constraint(
  propt &solver,
  const bmc_mapt &bmc_map,
  const exprt &expr,
  unsigned current, unsigned next,
  const namespacet &ns,
  messaget &message);

literalt instantiate_convert(
  propt &solver,
  const bmc_mapt &bmc_map,
  const exprt &expr,
  unsigned current, unsigned next,
  const namespacet &ns,
  messaget &message);
  
void instantiate_convert(
  propt &solver,
  const bmc_mapt &bmc_map,
  const exprt &expr,
  unsigned current, unsigned next,
  const namespacet &ns,
  messaget &message,
  bvt &bv);

// word level

void instantiate(
  decision_proceduret &decision_procedure,
  const exprt &expr,
  unsigned current,
  const namespacet &ns);

literalt instantiate_convert(
  prop_convt &prop_conv,
  const exprt &expr,
  unsigned current,
  const namespacet &ns);

void instantiate(
  exprt &expr,
  unsigned current,
  const namespacet &ns);

std::string timeframe_identifier(
  unsigned timeframe,
  const irep_idt &identifier);

#endif
