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
    else if(always_expr.upper().is_constant())
    {
      auto lower_int = numeric_cast_v<mp_integer>(always_expr.lower());
      auto upper_int =
        numeric_cast_v<mp_integer>(to_constant_expr(always_expr.upper()));
      return lower_int >= 0 && lower_int <= 1 && upper_int >= 0 &&
             upper_int <= 1;
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
      auto lower_int = numeric_cast_v<mp_integer>(s_always_expr.lower());
      auto upper_int = numeric_cast_v<mp_integer>(s_always_expr.upper());
      return lower_int >= 0 && lower_int <= 1 && upper_int >= 0 &&
             upper_int <= 1;
    }
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
        property.proved();
      else
        property.unknown();
    }
  }

  return result;
}
