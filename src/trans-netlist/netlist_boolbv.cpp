/*******************************************************************\

Module: boolbvt for Netlists

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "netlist_boolbv.h"

#include <ebmc/ebmc_error.h>
#include <verilog/sva_expr.h>

/*******************************************************************\

Function: netlist_boolbvt::convert_bool

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt netlist_boolbvt::convert_bool(const exprt &expr)
{
  if(expr.id() == ID_symbol || expr.id() == ID_next_symbol)
  {
    bvt result = convert_bitvector(expr);

    if(result.size() != 1)
      throw "expected one-bit result";

    return result[0];
  }
  else if(expr.id() == ID_sva_overlapped_implication)
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

Function: netlist_boolbvt::convert_bitvector

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt netlist_boolbvt::convert_bitvector(const exprt &expr)
{
  if(expr.id() == ID_symbol || expr.id() == ID_next_symbol)
  {
    bool next = (expr.id() == ID_next_symbol);
    const irep_idt &identifier = expr.get(ID_identifier);

    std::size_t width = boolbv_width(expr.type());

    if(width != 0)
    {
      bvt bv;
      bv.resize(width);

      for(std::size_t i = 0; i < width; i++)
        bv[i] = next ? var_map.get_next(identifier, i)
                     : var_map.get_current(identifier, i);

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

Function: netlist_boolbvt::get_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt
netlist_boolbvt::get_literal(const std::string &symbol, const unsigned bit)
{
  return var_map.get_current(symbol, bit);
}
