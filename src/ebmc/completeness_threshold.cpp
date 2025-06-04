/*******************************************************************\

Module: Completeness Threshold

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "completeness_threshold.h"

#include <util/arith_tools.h>

#include <temporal-logic/ltl.h>
#include <temporal-logic/temporal_logic.h>
#include <verilog/sva_expr.h>

#include "bmc.h"

bool has_low_completeness_threshold(const exprt &expr)
{
  if(!has_temporal_operator(expr))
  {
    return true; // state predicate only
  }
  else if(expr.id() == ID_X)
  {
    // X p
    return !has_temporal_operator(to_X_expr(expr).op());
  }
  else if(
    expr.id() == ID_sva_nexttime || expr.id() == ID_sva_s_nexttime ||
    expr.id() == ID_sva_s_nexttime)
  {
    // these are rewritten to always/s_always by normalize_property
    PRECONDITION(false);
  }
  else if(expr.id() == ID_sva_ranged_always)
  {
    auto &always_expr = to_sva_ranged_always_expr(expr);
    if(has_temporal_operator(always_expr.op()))
      return false;
    else if(always_expr.to().is_constant())
    {
      auto from_int = numeric_cast_v<mp_integer>(always_expr.from());
      auto to_int =
        numeric_cast_v<mp_integer>(to_constant_expr(always_expr.to()));
      return from_int >= 0 && from_int <= 1 && to_int >= 0 && to_int <= 1;
    }
    else
      return false;
  }
  else if(expr.id() == ID_sva_s_always)
  {
    auto &s_always_expr = to_sva_s_always_expr(expr);
    if(has_temporal_operator(s_always_expr.op()))
      return false;
    else
    {
      auto from_int = numeric_cast_v<mp_integer>(s_always_expr.from());
      auto to_int = numeric_cast_v<mp_integer>(s_always_expr.to());
      return from_int >= 0 && from_int <= 1 && to_int >= 0 && to_int <= 1;
    }
  }
  else if(
    expr.id() == ID_sva_strong || expr.id() == ID_sva_weak ||
    expr.id() == ID_sva_implicit_strong || expr.id() == ID_sva_implicit_weak)
  {
    auto &sequence = to_sva_sequence_property_expr_base(expr).sequence();
    return has_low_completeness_threshold(sequence);
  }
  else if(expr.id() == ID_sva_boolean)
  {
    return true;
  }
  else if(expr.id() == ID_sva_or || expr.id() == ID_sva_and)
  {
    for(auto &op : expr.operands())
      if(!has_low_completeness_threshold(op))
        return false;
    return true;
  }
  else if(expr.id() == ID_sva_sequence_property)
  {
    PRECONDITION(false); // should have been turned into implicit weak/strong
  }
  else
    return false;
}

bool has_low_completeness_threshold(const ebmc_propertiest::propertyt &property)
{
  return has_low_completeness_threshold(property.normalized_expr);
}

bool have_low_completeness_threshold(const ebmc_propertiest &properties)
{
  for(auto &property : properties.properties)
    if(has_low_completeness_threshold(property))
      return true;
  return false;
}

property_checker_resultt completeness_threshold(
  const cmdlinet &cmdline,
  const transition_systemt &transition_system,
  const ebmc_propertiest &properties,
  const ebmc_solver_factoryt &solver_factory,
  message_handlert &message_handler)
{
  // Do we have an eligibile property?
  if(!have_low_completeness_threshold(properties))
    return property_checker_resultt{properties}; // give up

  // Do BMC with two timeframes
  auto result = bmc(
    1,     // bound
    false, // convert_only
    cmdline.isset("bmc-with-assumptions"),
    transition_system,
    properties,
    solver_factory,
    message_handler);

  for(auto &property : result.properties)
  {
    if(property.is_proved_with_bound())
    {
      // Turn "PROVED up to bound k" into "PROVED" if k>=CT
      if(has_low_completeness_threshold(property) && property.bound >= 1)
        property.proved("CT=1");
      else
        property.unknown();
    }
  }

  return result;
}
