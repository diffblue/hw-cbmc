/*******************************************************************\

Module: Ranking Neural Net

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "ranking_net.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/std_expr.h>

exprt wrap_around(exprt expr)
{
  // map negative values to positive ones, wrap around:
  // -1 --> int_max-1, -2 --> int_max-2, etc.
  auto int_max = to_signedbv_type(expr.type()).largest_expr();
  return if_exprt{sign_exprt{expr}, plus_exprt{int_max, expr}, expr};
}

tuple_exprt wrap_around_tuple(tuple_exprt expr)
{
  // map negative values to positive ones, wrap around:
  // -1 --> int_max-1, -2 --> int_max-2, etc.
  for(auto &op : expr.operands())
    op = wrap_around(op);

  return expr;
}

tuple_exprt ranking_nett::forward(const tuple_exprt &inputs) const
{
  auto fc1_out = fc1.forward(inputs);
  auto w_out = wrap_around_tuple(fc1_out);
  return w_out;
}

ranking_nett::lineart::lineart(
  const irep_idt &__name,
  std::size_t in,
  std::size_t out,
  const typet &type)
  : name(__name)
{
  neurons.reserve(out);

  for(std::size_t i = 0; i < out; i++)
  {
    irep_idt identifier = id2string(__name) + ".n" + std::to_string(i);
    neurons.emplace_back(identifier, in, type);
  }
}

ranking_nett::lineart::neuront::neuront(
  const irep_idt &__name,
  std::size_t in,
  const typet &type)
  : name(__name)
{
  {
    irep_idt identifier = id2string(__name) + ".b";
    bias = symbol_exprt(identifier, type);
  }

  weights.reserve(in);

  for(std::size_t i = 0; i < in; i++)
  {
    irep_idt identifier = id2string(__name) + ".w" + std::to_string(i);
    weights.emplace_back(symbol_exprt{identifier, type});
  }
}

exprt ranking_nett::lineart::neuront::forward(const tuple_exprt &input) const
{
  exprt::operandst result;
  result.reserve(weights.size() + 1); // one more for bias

  result.push_back(bias);

  PRECONDITION(weights.size() == input.operands().size());

  for(std::size_t i = 0; i < weights.size(); i++)
    result.push_back(mult_exprt{weights[i], input.operands()[i]});

  return plus_exprt{std::move(result), bias.type()};
}

exprt relu(exprt expr)
{
  auto zero = from_integer(0, expr.type());
  return if_exprt{greater_than_or_equal_exprt{expr, zero}, expr, zero};
}

tuple_exprt ranking_nett::lineart::forward(const tuple_exprt &input) const
{
  tuple_exprt::operandst result;
  result.reserve(neurons.size());

  for(auto &neuron : neurons)
    result.push_back(neuron.forward(input));

  return tuple_exprt{std::move(result)};
}
