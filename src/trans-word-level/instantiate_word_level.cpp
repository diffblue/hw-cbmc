/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "instantiate_word_level.h"

#include <util/ebmc_util.h>
#include <util/expr_util.h>

#include <ebmc/ebmc_error.h>
#include <temporal-logic/temporal_expr.h>
#include <temporal-logic/temporal_logic.h>
#include <verilog/sva_expr.h>
#include <verilog/verilog_expr.h>

#include "sequence.h"

/*******************************************************************\

Function: timeframe_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string
timeframe_identifier(const mp_integer &timeframe, const irep_idt &identifier)
{
  return id2string(identifier) + "@" + integer2string(timeframe);
}

/*******************************************************************\

Function: timeframe_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt timeframe_symbol(const mp_integer &timeframe, symbol_exprt src)
{
  auto result = std::move(src);
  result.set_identifier(
    timeframe_identifier(timeframe, result.get_identifier()));
  return result;
}

/*******************************************************************\

   Class: wl_instantiatet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class wl_instantiatet
{
public:
  wl_instantiatet(const mp_integer &_no_timeframes, bool _next_symbol_allowed)
    : no_timeframes(_no_timeframes), next_symbol_allowed(_next_symbol_allowed)
  {
  }

  /// Instantiate the given expression for timeframe t
  [[nodiscard]] exprt operator()(exprt expr, const mp_integer &t) const
  {
    return instantiate_rec(std::move(expr), t);
  }

protected:
  const mp_integer &no_timeframes;
  bool next_symbol_allowed;

  [[nodiscard]] exprt instantiate_rec(exprt, const mp_integer &t) const;
  [[nodiscard]] typet instantiate_rec(typet, const mp_integer &t) const;
};

/*******************************************************************\

Function: wl_instantiatet::instantiate_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt wl_instantiatet::instantiate_rec(exprt expr, const mp_integer &t) const
{
  expr.type() = instantiate_rec(expr.type(), t);

  if(expr.id() == ID_next_symbol)
  {
    PRECONDITION(next_symbol_allowed);
    expr.id(ID_symbol);
    auto u = t + 1;
    return timeframe_symbol(u, to_symbol_expr(std::move(expr)));
  }
  else if(expr.id() == ID_symbol)
  {
    return timeframe_symbol(t, to_symbol_expr(std::move(expr)));
  }
  else if(
    expr.id() == ID_typecast && expr.type().id() == ID_bool &&
    to_typecast_expr(expr).op().type().id() == ID_verilog_sva_sequence)
  {
    // should have been done by property_obligations_rec
    PRECONDITION(false);
  }
  else if(
    expr.id() == ID_sva_sequence_property || expr.id() == ID_sva_weak ||
    expr.id() == ID_sva_strong)
  {
    // should have been done by property_obligations_rec
    PRECONDITION(false);
  }
  else if(expr.id() == ID_verilog_past)
  {
    auto &verilog_past = to_verilog_past_expr(expr);

    mp_integer ticks;
    if(to_integer_non_constant(verilog_past.ticks(), ticks))
      throw "failed to convert $past number of ticks";

    if(ticks > t)
    {
      // return the 'default value' for the type
      return verilog_past.default_value();
    }
    else
    {
      return instantiate_rec(verilog_past.what(), t - ticks);
    }
  }
  else if(is_temporal_operator(expr))
  {
    // should have been done by property_obligations_rec
    throw ebmc_errort() << "instantiate_word_level got temporal operator "
                        << expr.id();
  }
  else
  {
    for(auto &op : expr.operands())
    {
      op = instantiate_rec(op, t);
    }

    return expr;
  }
}

/*******************************************************************\

Function: wl_instantiatet::instantiate_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet wl_instantiatet::instantiate_rec(typet type, const mp_integer &) const
{
  return type;
}

/*******************************************************************\

Function: instantiate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt instantiate(
  const exprt &expr,
  const mp_integer &t,
  const mp_integer &no_timeframes)
{
  wl_instantiatet wl_instantiate(no_timeframes, true);
  return wl_instantiate(expr, t);
}

/*******************************************************************\

Function: instantiate_state_predicate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt instantiate_state_predicate(
  const exprt &expr,
  const mp_integer &current,
  const mp_integer &no_timeframes)
{
  PRECONDITION(expr.type().id() == ID_bool);
  wl_instantiatet wl_instantiate(no_timeframes, false);
  return wl_instantiate(expr, current);
}
