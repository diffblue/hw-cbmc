/*******************************************************************\

Module: New IC3 Engine

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Bit-level IC3/PDR engine operating on the netlist (AIG) encoding
/// of the transition system. The netlist is encoded once into CNF,
/// with the next-state functions available as literals in the same
/// variable space, so a single timeframe copy suffices.
/// Inspired by rIC3 (arXiv:2502.13605).

#include "new_ic3_engine.h"

#include <ebmc/ebmc_error.h>
#include <ebmc/liveness_to_safety.h>
#include <ebmc/netlist.h>
#include <ebmc/report_results.h>
#include <temporal-logic/ctl.h>
#include <temporal-logic/ltl.h>
#include <temporal-logic/temporal_logic.h>
#include <trans-netlist/aig_prop.h>
#include <trans-netlist/instantiate_netlist.h>
#include <verilog/sva_expr.h>

#include "ic3_solver.h"

static bool new_ic3_supports_property(const exprt &expr)
{
  if(!is_temporal_operator(expr))
    return false;
  if(expr.id() == ID_sva_always)
    return !has_temporal_operator(to_sva_always_expr(expr).op());
  if(expr.id() == ID_G)
    return !has_temporal_operator(to_G_expr(expr).op());
  if(expr.id() == ID_AG)
    return !has_temporal_operator(to_AG_expr(expr).op());
  return false;
}

property_checker_resultt new_ic3_engine(
  const cmdlinet &cmdline,
  transition_systemt &transition_system,
  ebmc_propertiest &properties,
  message_handlert &message_handler)
{
  messaget message{message_handler};

  if(!properties.has_unfinished_property())
    return property_checker_resultt{properties};

  if(cmdline.isset("liveness-to-safety"))
    liveness_to_safety(transition_system, properties);

  for(auto &property : properties.properties)
  {
    if(property.is_assumed())
    {
      message.error() << "no support for assumptions" << messaget::eom;
      return property_checker_resultt::error();
    }
  }

  const namespacet ns(transition_system.symbol_table);

  auto netlist =
    make_netlist(transition_system, properties, cmdline, message_handler);

  message.statistics() << "Latches: " << netlist.var_map.latches.size()
                       << ", nodes: " << netlist.number_of_nodes()
                       << messaget::eom;

  for(auto &property : properties.properties)
  {
    if(property.is_disabled() || !property.is_unknown())
      continue;

    if(!new_ic3_supports_property(property.normalized_expr))
    {
      property.failure("property not supported by new IC3 engine");
      continue;
    }

    message.status() << "Checking " << property.name << " with new IC3 engine"
                     << messaget::eom;

    // Add the property cone to a local copy of the netlist and obtain
    // the property literal in the AIG variable space.
    netlistt prop_netlist(netlist);
    literalt prop_lit;
    {
      aig_prop_constraintt aig_prop(prop_netlist, message_handler);
      prop_lit = instantiate_convert(
        aig_prop,
        prop_netlist.var_map,
        to_unary_expr(property.normalized_expr).op(),
        ns,
        message_handler);
    }

    ic3_solvert solver{prop_netlist, prop_lit, message_handler};
    auto result = solver.solve();

    // For exists-path properties (cover), the normalized expression is
    // the dual safety property: a refutation is a witness trace, and a
    // proof shows that no witness exists.
    switch(result)
    {
    case ic3_resultt::PROVED:
      if(property.is_exists_path())
        property.refuted();
      else
        property.proved();
      break;
    case ic3_resultt::REFUTED:
      if(property.is_exists_path())
        property.proved();
      else
        property.refuted();
      break;
    }
  }

  return property_checker_resultt{properties};
}
