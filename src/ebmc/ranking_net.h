/*******************************************************************\

Module: Ranking Neural Net

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef EBMC_RANKING_NET_H
#define EBMC_RANKING_NET_H

#include <util/mathematical_expr.h>

exprt relu(exprt);
exprt wrap_around(exprt);

class ranking_nett
{
public:
  explicit ranking_nett(
    std::size_t number_of_state_variables,
    std::size_t fc1_neurons,
    const typet &__type)
    : fc1("nn::fc1", number_of_state_variables, fc1_neurons, __type)
  {
  }

  tuple_exprt forward(const tuple_exprt &inputs) const;

  class lineart
  {
  public:
    lineart(
      const irep_idt &name,
      std::size_t in,
      std::size_t out,
      const typet &);

    irep_idt name;

    class neuront
    {
    public:
      std::vector<exprt> weights;
      exprt bias;
      irep_idt name;
      neuront(const irep_idt &name, std::size_t in, const typet &);
      exprt forward(const tuple_exprt &) const;
    };

    std::vector<neuront> neurons;

    tuple_exprt forward(const tuple_exprt &) const;
  };

  lineart fc1;
};

#endif // EBMC_RANKING_NET
