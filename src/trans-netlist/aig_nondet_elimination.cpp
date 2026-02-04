/*******************************************************************\

Module: AIG Nondet Elimination

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// AIG Nondet Elimination

#include "aig_nondet_elimination.h"

#include "aig_reorder.h"

#include <set>

std::pair<aigt, aig_substitution_mapt> aig_nondet_elimination(
  const aigt &old_aig,
  const aig_plus_constraintst::equivalencest &equivalences)
{
  const auto num_nodes = old_aig.number_of_nodes();

  // Build substitution map for nondet (input) nodes.
  // subst[var_no] gives the replacement literal for an eliminated node.
  // Identity (literalt(var_no, false)) means the node is not eliminated.
  aig_substitution_mapt subst{num_nodes};

  for(const auto &[a, b] : equivalences)
  {
    bool a_is_input = !a.is_constant() && old_aig.nodes[a.var_no()].is_input();
    bool b_is_input = !b.is_constant() && old_aig.nodes[b.var_no()].is_input();
    bool a_not_yet_subst =
      a_is_input && subst[a.var_no()] == literalt(a.var_no(), false);
    bool b_not_yet_subst =
      b_is_input && subst[b.var_no()] == literalt(b.var_no(), false);

    if(a_not_yet_subst && !b_not_yet_subst)
      subst[a.var_no()] = b ^ a.sign();
    else if(b_not_yet_subst && !a_not_yet_subst)
      subst[b.var_no()] = a ^ b.sign();
    else if(a_not_yet_subst && b_not_yet_subst)
    {
      // Both are unsubstituted nondets. Eliminate the first.
      subst[a.var_no()] = b ^ a.sign();
    }
  }

  // Resolve substitution chains and detect cycles.
  for(std::size_t i = 0; i < num_nodes; i++)
  {
    auto i_var_no = narrow_cast<literalt::var_not>(i);
    if(subst[i] == literalt(i_var_no, false))
      continue; // not eliminated

    literalt current = subst[i];
    std::set<literalt::var_not> visited;
    visited.insert(i_var_no);
    bool cycle = false;

    while(!current.is_constant())
    {
      auto var = current.var_no();
      if(subst[var] == literalt(var, false))
        break; // reached a non-eliminated node
      if(visited.count(var))
      {
        cycle = true;
        break;
      }
      visited.insert(var);
      current = subst[var] ^ current.sign();
    }

    if(cycle)
      subst[i] = literalt(i_var_no, false); // un-eliminate
    else
      subst[i] = current; // resolved target
  }

  // Rebuild the AIG in dependency order.
  return aig_reorder(old_aig, subst);
}
