/*******************************************************************\

Module: Unwinding Netlists

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "unwind_netlist.h"

#include <util/ebmc_util.h>
#include <util/expr_util.h>

#include <solvers/prop/literal_expr.h>
#include <temporal-logic/ctl.h>
#include <temporal-logic/ltl.h>
#include <temporal-logic/temporal_logic.h>
#include <verilog/sva_expr.h>

#include "instantiate_netlist.h"

/*******************************************************************\

Function: unwind

  Inputs:

 Outputs:

 Purpose: Unwind timeframe by timeframe

\*******************************************************************/

void unwind(
  const netlistt &netlist,
  const bmc_mapt &bmc_map,
  messaget &message,
  cnft &solver,
  bool add_initial_state,
  std::size_t t)
{
  bool first=(t==0);
  bool last=(t==bmc_map.timeframe_map.size()-1);

  if(add_initial_state && first)
  {
    // do initial state
    message.progress() << "Initial State" << messaget::eom;

    for(const auto & n : netlist.initial)
      solver.l_set_to(bmc_map.translate(0, n), true);
  }

  // do transitions
  if(last)
    message.progress() << "Transition " << t << messaget::eom;
  else
    message.progress() << "Transition " << t << "->" << t + 1 << messaget::eom;

  const bmc_mapt::timeframet &timeframe=bmc_map.timeframe_map[t];
  
  for(std::size_t n=0; n<timeframe.size(); n++)
  {
    const aig_nodet &node=netlist.get_node(literalt(n, false));

    if(node.is_and())
    {
      literalt la=bmc_map.translate(t, node.a);
      literalt lb=bmc_map.translate(t, node.b);

      cnf_gate_and(solver, la, lb, timeframe[n].solver_literal);
    }
  }

  // general AIG constraints
  for(const auto & c : netlist.constraints)
    solver.l_set_to(bmc_map.translate(t, c), true);

  // transition constraints
  for(const auto & c : netlist.transition)
    solver.l_set_to(bmc_map.translate(t, c), true);

  if(!last)
  {     
    // joining the latches between timeframe and timeframe+1
    for(auto v_it : netlist.var_map.sorted())
    {
      const var_mapt::vart &var=v_it->second;
      if(var.is_latch())
      {
        for(std::size_t bit_nr=0; bit_nr<var.bits.size(); bit_nr++)
        {
          const var_mapt::vart::bitt &bit=var.bits[bit_nr];
          
          literalt l_from=bit.next;
          literalt l_to=bit.current;

          solver.set_equal(
            bmc_map.translate(t, l_from),
            bmc_map.translate(t+1, l_to));
        }
      }
    }
  }
}

/*******************************************************************\

Function: unwind

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void unwind(
  const netlistt &netlist,
  const bmc_mapt &bmc_map,
  messaget &message,
  cnft &solver,
  bool add_initial_state)
{
  for(std::size_t t = 0; t < bmc_map.timeframe_map.size(); t++)
    unwind(netlist, bmc_map, message, solver, add_initial_state, t);
}

/*******************************************************************\

Function: unwind_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt unwind_property(const exprt &property_expr, const bmc_mapt &bmc_map)
{
  bvt prop_bv{bmc_map.timeframe_map.size()};

  // We only do Gp/AGp
  PRECONDITION(
    is_Gp(property_expr) || is_AGp(property_expr) ||
    is_SVA_always_p(property_expr));

  auto &p = to_unary_expr(property_expr).op();
  PRECONDITION(p.id() == ID_literal);

  auto p_node = to_literal_expr(p).get_literal();

  for(std::size_t t = 0; t < bmc_map.timeframe_map.size(); t++)
  {
    literalt l = bmc_map.translate(t, p_node);
    prop_bv[t]=l;
  }

  return prop_bv;
}

/*******************************************************************\

Function: netlist_bmc_supports_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool netlist_bmc_supports_property(const exprt &expr)
{
  // No $past.
  if(has_subexpr(expr, ID_verilog_past))
    return false;

  // We do AG p only.
  if(expr.id() == ID_AG)
    return !has_temporal_operator(to_AG_expr(expr).op());
  else if(expr.id() == ID_G)
    return !has_temporal_operator(to_G_expr(expr).op());
  else if(expr.id() == ID_sva_always)
    return !has_temporal_operator(to_sva_always_expr(expr).op());
  else
    return false;
}
