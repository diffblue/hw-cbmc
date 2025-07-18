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

// counting number of transitions
std::optional<mp_integer> completeness_threshold(const exprt &expr)
{
  if(!has_temporal_operator(expr))
  {
    return 0; // state predicate only
  }
  else if(expr.id() == ID_X)
  {
    // X p
    // Increases the CT by one.
    auto ct_p = completeness_threshold(to_X_expr(expr).op());
    if(ct_p.has_value())
      return *ct_p + 1;
    else
      return {};
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
      return {};

    if(always_expr.is_range() && !always_expr.is_unbounded())
    {
      auto to_int =
        numeric_cast_v<mp_integer>(to_constant_expr(always_expr.to()));

      // increases the CT by to_int
      auto ct_op = completeness_threshold(always_expr.op());
      if(ct_op.has_value())
        return *ct_op + to_int;
      else
        return {};
    }
    else
      return {};
  }
  else if(expr.id() == ID_sva_s_always)
  {
    auto &s_always_expr = to_sva_s_always_expr(expr);

    auto to_int = numeric_cast_v<mp_integer>(s_always_expr.to());

    if(to_int < 0)
      return {};

    // increases the CT by to_int
    auto ct_op = completeness_threshold(s_always_expr.op());
    if(ct_op.has_value())
      return *ct_op + to_int;
    else
      return {};
  }
  else if(
    expr.id() == ID_sva_strong || expr.id() == ID_sva_weak ||
    expr.id() == ID_sva_implicit_strong || expr.id() == ID_sva_implicit_weak)
  {
    auto &sequence = to_sva_sequence_property_expr_base(expr).sequence();
    return completeness_threshold(sequence);
  }
  else if(expr.id() == ID_sva_boolean)
  {
    return 0; // state predicate only
  }
  else if(expr.id() == ID_sva_cycle_delay)
  {
    auto &cycle_delay = to_sva_cycle_delay_expr(expr);
    mp_integer ct_lhs = 0;

    if(cycle_delay.lhs().is_not_nil())
    {
      auto ct_lhs_opt = completeness_threshold(cycle_delay.lhs());
      if(ct_lhs_opt.has_value())
        ct_lhs = ct_lhs_opt.value();
      else
        return {};
    }

    if(cycle_delay.is_range())
      return {};
    else // singleton
    {
      auto ct_rhs = completeness_threshold(cycle_delay.rhs());
      if(ct_rhs.has_value())
        return ct_lhs + numeric_cast_v<mp_integer>(cycle_delay.from()) +
               *ct_rhs;
      else
        return {};
    }
  }
  else if(expr.id() == ID_sva_sequence_property)
  {
    PRECONDITION(false); // should have been turned into implicit weak/strong
  }
  else
    return {};
}

std::optional<mp_integer>
completeness_threshold(const ebmc_propertiest::propertyt &property)
{
  return completeness_threshold(property.normalized_expr);
}

std::optional<mp_integer>
completeness_threshold(const ebmc_propertiest &properties)
{
  std::optional<mp_integer> max_ct;

  for(auto &property : properties.properties)
  {
    auto ct_opt = completeness_threshold(property);
    if(ct_opt.has_value())
      max_ct = std::max(max_ct.value_or(0), *ct_opt);
  }

  return max_ct;
}

property_checker_resultt completeness_threshold(
  const cmdlinet &cmdline,
  const transition_systemt &transition_system,
  const ebmc_propertiest &properties,
  const ebmc_solver_factoryt &solver_factory,
  message_handlert &message_handler)
{
  // Do we have an eligible property?
  auto ct_opt = completeness_threshold(properties);

  if(!ct_opt.has_value())
    return property_checker_resultt{properties}; // give up

  // Do BMC, using the CT as the bound
  auto result = bmc(
    numeric_cast_v<std::size_t>(*ct_opt), // bound
    false,                                // convert_only
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
      auto property_ct_opt = completeness_threshold(property);
      if(property_ct_opt.has_value())
        property.proved("CT=" + integer2string(*property_ct_opt));
      else
        property.unknown();
    }
  }

  return result;
}
