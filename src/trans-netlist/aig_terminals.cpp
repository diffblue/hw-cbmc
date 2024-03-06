/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "aig_terminals.h"

const aig_terminal_sett &get_terminals_rec(
  const aigt &aig,
  literalt::var_not n,
  aig_terminalst &terminals)
{
  PRECONDITION(n < aig.nodes.size());

  auto it = terminals.find(n);

  if(it != terminals.end())
    return it->second; // already done

  const aig_nodet &node = aig.nodes[n];

  auto &t = terminals[n];

  if(node.is_and())
  {
    if(!node.a.is_constant())
    {
      const std::set<literalt::var_not> &ta =
        get_terminals_rec(aig, node.a.var_no(), terminals);
      t.insert(ta.begin(), ta.end());
    }

    if(!node.b.is_constant())
    {
      const std::set<literalt::var_not> &tb =
        get_terminals_rec(aig, node.b.var_no(), terminals);
      t.insert(tb.begin(), tb.end());
    }
  }
  else // this is a terminal
  {
    t.insert(n);
  }

  return t;
}

aig_terminalst terminals(const aigt &aig)
{
  aig_terminalst terminals;

  for(aigt::nodest::size_type n = 0; n < aig.nodes.size(); n++)
    get_terminals_rec(aig, n, terminals);

  return terminals;
}
