/*******************************************************************\

Module: Completeness Threshold

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "completeness_threshold.h"

#include <util/arith_tools.h>
#include <util/pointer_offset_size.h>
#include <util/std_types.h>

#include <temporal-logic/ctl.h>
#include <temporal-logic/ltl.h>
#include <temporal-logic/nnf.h>
#include <temporal-logic/temporal_logic.h>
#include <verilog/sva_expr.h>

#include "bmc.h"
#include "transition_system.h"

/// An upper bound on the recurrence diameter of the state space.
/// A purely combinational circuit (no state variables) has diameter 0.
/// A sequential circuit with n state bits has diameter at most 2^n - 1.
std::optional<mp_integer>
recurrence_diameter(const transition_systemt &transition_system)
{
  mp_integer total_bits = 0;
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  for(auto &var : transition_system.state_variables())
  {
    auto bits = pointer_offset_bits(var.type(), ns);
    if(!bits.has_value())
      return {};
    total_bits += *bits;
  }

  if(total_bits > 8)
    return {};

  return power(mp_integer{2}, total_bits) - 1;
}

/// Completeness threshold for given property.
/// Counting number of transitions.
/// May use recurrence diameter if available.
std::optional<mp_integer>
completeness_threshold(const exprt &expr, const std::optional<mp_integer> &rd)
{
  if(!has_temporal_operator(expr))
  {
    return 0; // state predicate only
  }
  else if(expr.id() == ID_X)
  {
    // X p
    // Increases the CT by one.
    auto ct_p = completeness_threshold(to_X_expr(expr).op(), rd);
    if(ct_p.has_value())
      return *ct_p + 1;
    else
      return {};
  }
  else if(expr.id() == ID_sva_nexttime || expr.id() == ID_sva_s_nexttime)
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
      auto ct_op = completeness_threshold(always_expr.op(), rd);
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
    auto ct_op = completeness_threshold(s_always_expr.op(), rd);
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
    return completeness_threshold(sequence, rd);
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
      auto ct_lhs_opt = completeness_threshold(cycle_delay.lhs(), rd);
      if(ct_lhs_opt.has_value())
        ct_lhs = ct_lhs_opt.value();
      else
        return {};
    }

    if(cycle_delay.is_range())
      return {};
    else // singleton
    {
      auto ct_rhs = completeness_threshold(cycle_delay.rhs(), rd);
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
  else if(
    is_Gp(expr) || is_Fp(expr) || is_SVA_always_p(expr) ||
    is_SVA_s_eventually_p(expr))
  {
    // the recurrence diameter is a CT
    return rd;
  }
  else
    return {};
}

std::optional<mp_integer> completeness_threshold(
  const ebmc_propertiest::propertyt &property,
  const std::optional<mp_integer> &rd)
{
  return completeness_threshold(property.normalized_expr, rd);
}

std::optional<mp_integer> max_completeness_threshold(
  const ebmc_propertiest &properties,
  const std::optional<mp_integer> &rd)
{
  std::optional<mp_integer> max_ct;

  for(auto &property : properties.properties)
  {
    auto ct_opt = completeness_threshold(property, rd);
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
  auto rd_opt = recurrence_diameter(transition_system);
  auto max_ct_opt = max_completeness_threshold(properties, rd_opt);

  if(!max_ct_opt.has_value())
    return property_checker_resultt{properties}; // give up

  // Do BMC, using the max CT as the bound
  auto &bound = max_ct_opt.value();

  auto result = bmc(
    numeric_cast_v<std::size_t>(bound), // bound
    false,                              // convert_only
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
      auto property_ct_opt = completeness_threshold(property, rd_opt);

      if(property_ct_opt.has_value() && property_ct_opt.value() >= bound)
        property.proved("CT=" + integer2string(*property_ct_opt));
      else
        property.unknown();
    }
  }

  return result;
}
