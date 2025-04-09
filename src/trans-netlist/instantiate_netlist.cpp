/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "instantiate_netlist.h"

#include <util/ebmc_util.h>
#include <util/expr_util.h>
#include <util/std_expr.h>

#include <ebmc/ebmc_error.h>
#include <solvers/flattening/boolbv.h>
#include <solvers/prop/literal_expr.h>
#include <temporal-logic/temporal_logic.h>
#include <verilog/sva_expr.h>

#include <cassert>
#include <cstdlib>

/*******************************************************************\

   Class: instantiate_var_mapt

 Purpose:

\*******************************************************************/

class instantiate_var_mapt:public boolbvt
{
public:
  instantiate_var_mapt(const namespacet &_ns, propt &solver,
                       message_handlert &message_handler,
                       const var_mapt &_var_map)
      : boolbvt(_ns, solver, message_handler), var_map(_var_map) {}

  typedef boolbvt SUB;

  // overloading
  using boolbvt::get_literal;
  
  virtual literalt convert_bool(const exprt &expr);
  virtual literalt get_literal(const std::string &symbol, const unsigned bit);
  virtual bvt convert_bitvector(const exprt &expr);
   
protected:   
  // disable smart variable allocation,
  // we already have literals for all variables
  virtual bool boolbv_set_equality_to_true(const equal_exprt &expr) { return true; }
  virtual bool set_equality_to_true(const equal_exprt &expr) { return true; }
  
  const var_mapt &var_map;
};

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
  instantiate_var_mapt i(ns, solver, message_handler, var_map);

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
  instantiate_var_mapt i(ns, solver, message_handler, var_map);

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
  instantiate_var_mapt i(ns, solver, message_handler, var_map);

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

Function: instantiate_var_mapt::convert_bool

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt instantiate_var_mapt::convert_bool(const exprt &expr)
{
  if(expr.id()==ID_symbol || expr.id()==ID_next_symbol)
  {
    bvt result=convert_bitvector(expr);

    if(result.size()!=1)
      throw "expected one-bit result";

    return result[0];
  }
  else if(expr.id()==ID_sva_overlapped_implication)
  {
    // same as regular implication
    auto &sva_overlapped_implication = to_sva_overlapped_implication_expr(expr);
    return prop.limplies(
      convert_bool(sva_overlapped_implication.lhs()),
      convert_bool(sva_overlapped_implication.rhs()));
  }
  else if(expr.id() == ID_verilog_past)
  {
    throw ebmc_errort().with_location(expr.source_location())
      << "no support for $past when using AIG backends";
  }

  return SUB::convert_bool(expr);
}

/*******************************************************************\

Function: instantiate_var_mapt::convert_bitvector

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt instantiate_var_mapt::convert_bitvector(const exprt &expr)
{
  if(expr.id()==ID_symbol || expr.id()==ID_next_symbol)
  {
    bool next=(expr.id()==ID_next_symbol);
    const irep_idt &identifier=expr.get(ID_identifier);

    std::size_t width=boolbv_width(expr.type());

    if(width!=0)
    {
      bvt bv;
      bv.resize(width);

      for(std::size_t i=0; i<width; i++)
        bv[i]=next?var_map.get_next(identifier, i)
                  :var_map.get_current(identifier, i);

      return bv;
    }
  }
  else if(expr.id() == ID_verilog_past)
  {
    throw ebmc_errort().with_location(expr.source_location())
      << "no support for $past when using AIG backends";
  }

  return SUB::convert_bitvector(expr);
}

/*******************************************************************\

Function: instantiate_var_mapt::get_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt instantiate_var_mapt::get_literal(
  const std::string &symbol,
  const unsigned bit)
{
  return var_map.get_current(symbol, bit);
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
