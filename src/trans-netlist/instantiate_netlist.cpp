/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "instantiate_netlist.h"

#include <util/ebmc_util.h>
#include <util/expr_util.h>
#include <util/std_expr.h>

#include <ebmc/ebmc_error.h>
#include <solvers/prop/literal_expr.h>
#include <temporal-logic/temporal_logic.h>
#include <verilog/sva_expr.h>

#include "netlist_boolbv.h"

#include <cassert>
#include <cstdlib>

/*******************************************************************\

Function: instantiate_constraint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instantiate_constraint(
  propt &solver,
  const var_mapt &var_map,
  const exprt &expr,
  const namespacet &ns,
  message_handlert &message_handler)
{
  netlist_boolbvt i(ns, solver, message_handler, var_map);

  try
  {
    i.set_to_true(expr);
  }

  catch(const char *err)
  {
    messaget(message_handler).error() << err << messaget::eom;
    exit(1);
  }

  catch(const std::string &err)
  {
    messaget(message_handler).error() << err << messaget::eom;
    exit(1);
  }
}

/*******************************************************************\

Function: instantiate_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt instantiate_convert(
  propt &solver,
  const var_mapt &var_map,
  const exprt &expr,
  const namespacet &ns,
  message_handlert &message_handler)
{
  netlist_boolbvt i(ns, solver, message_handler, var_map);

  try
  {
    return i.convert(expr);
  }

  catch(const char *err)
  {
    messaget(message_handler).error() << err << messaget::eom;
    exit(1);
  }

  catch(const std::string &err)
  {
    messaget(message_handler).error() << err << messaget::eom;
    exit(1);
  }
}

/*******************************************************************\

Function: instantiate_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instantiate_convert(
  propt &solver,
  const var_mapt &var_map,
  const exprt &expr,
  const namespacet &ns,
  message_handlert &message_handler,
  bvt &bv)
{
  netlist_boolbvt i(ns, solver, message_handler, var_map);

  try
  {
    bv=i.convert_bitvector(expr);
  }

  catch(const char *err)
  {
    messaget(message_handler).error() << err << messaget::eom;
    exit(1);
  }

  catch(const std::string &err)
  {
    messaget(message_handler).error() << err << messaget::eom;
    exit(1);
  }
}

/*******************************************************************\

Function: netlist_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::optional<exprt> netlist_property(
  propt &solver,
  const var_mapt &var_map,
  const exprt &expr,
  const namespacet &ns,
  message_handlert &message_handler)
{
  if(is_temporal_operator(expr))
  {
    if(is_LTL_operator(expr) || is_CTL_operator(expr))
    {
      exprt copy = expr;
      for(auto &op : copy.operands())
      {
        auto op_opt =
          netlist_property(solver, var_map, op, ns, message_handler);
        if(op_opt.has_value())
          op = op_opt.value();
        else
          return {};
      }
      return copy;
    }
    else if(is_SVA_operator(expr))
    {
      // Try to turn into LTL
      auto LTL_opt = SVA_to_LTL(expr);
      if(LTL_opt.has_value())
        return netlist_property(solver, var_map, *LTL_opt, ns, message_handler);
      else
        return {};
    }
    else
      return {};
  }
  else if(!has_temporal_operator(expr))
  {
    auto l = instantiate_convert(solver, var_map, expr, ns, message_handler);
    return literal_exprt{l};
  }
  else if(
    expr.id() == ID_and || expr.id() == ID_or || expr.id() == ID_not ||
    expr.id() == ID_implies || expr.id() == ID_xor || expr.id() == ID_xnor)
  {
    exprt copy = expr;
    for(auto &op : copy.operands())
    {
      auto op_opt = netlist_property(solver, var_map, op, ns, message_handler);
      if(op_opt.has_value())
        op = op_opt.value();
      else
        return {};
    }
    return copy;
  }
  else
  {
    // contains temporal operator, but not propositional skeleton
    return {};
  }
}
