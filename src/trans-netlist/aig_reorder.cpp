/*******************************************************************\

Module: AIG Reorder

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// AIG Reorder

#include "aig_reorder.h"

#include <util/invariant.h>

#include <functional>

std::pair<aigt, aig_substitution_mapt>
aig_reorder(const aigt &old_aig, const aig_substitution_mapt &subst)
{
  const auto num_nodes = old_aig.number_of_nodes();

  aigt new_aig;
  aig_substitution_mapt new_map{num_nodes};

  enum class statet
  {
    UNVISITED,
    IN_PROGRESS,
    DONE
  };
  std::vector<statet> state(num_nodes, statet::UNVISITED);

  std::function<literalt(literalt)> translate = [&](literalt l) -> literalt
  {
    if(l.is_constant())
      return l;

    auto var = l.var_no();
    PRECONDITION(var < num_nodes);

    if(state[var] == statet::DONE)
      return new_map[var] ^ l.sign();

    INVARIANT(state[var] != statet::IN_PROGRESS, "cycle in AIG during reorder");
    state[var] = statet::IN_PROGRESS;

    bool is_eliminated = subst[var] != literalt{var, false};

    if(is_eliminated)
    {
      new_map[var] = translate(subst[var]);
    }
    else
    {
      const auto &node = old_aig.nodes[var];
      if(node.is_input())
      {
        new_map[var] = new_aig.new_input();
      }
      else
      {
        auto new_a = translate(node.a);
        auto new_b = translate(node.b);
        new_map[var] = new_aig.new_and_node(new_a, new_b);
      }
    }

    state[var] = statet::DONE;
    return new_map[var] ^ l.sign();
  };

  // Translate all nodes.
  for(std::size_t i = 0; i < num_nodes; i++)
  {
    if(state[i] == statet::UNVISITED)
      translate(literalt{narrow_cast<literalt::var_not>(i), false});
  }

  // Translate labeling.
  for(const auto &[label, lit] : old_aig.labeling)
    new_aig.labeling[label] = translate(lit);

  return {std::move(new_aig), std::move(new_map)};
}
