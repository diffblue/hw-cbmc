/*******************************************************************\

Module: Output AIGER

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "output_aiger.h"

#include <trans-netlist/netlist.h>

#include <ostream>

extern "C"
{
#include <ic3/aiger/aiger.h>
}

/// Convert a literalt to an AIGER literal.
/// AIGER uses variable 0 for the constant FALSE.
/// CBMC variables start at 0, so we map var_no v to AIGER variable v+1.
static unsigned to_aiger_lit(literalt l)
{
  if(l.is_false())
    return aiger_false;
  if(l.is_true())
    return aiger_true;
  return ((l.var_no() + 1) << 1) | (l.sign() ? 1u : 0u);
}

void output_aiger(const netlistt &netlist, std::ostream &out)
{
  aiger *aig = aiger_init();

  // Add inputs
  for(auto var_no : netlist.var_map.inputs)
  {
    unsigned lit = to_aiger_lit(literalt{var_no, false});
    aiger_add_input(aig, lit, nullptr);
  }

  // Add latches
  for(auto var_no : netlist.var_map.latches)
  {
    unsigned lit = to_aiger_lit(literalt{var_no, false});
    // Find the 'next' literal for this latch from the var_map
    auto it = netlist.var_map.reverse_map.find(var_no);
    PRECONDITION(it != netlist.var_map.reverse_map.end());
    literalt next = netlist.var_map.get_next(it->second);
    unsigned next_lit = to_aiger_lit(next);
    aiger_add_latch(aig, lit, next_lit, nullptr);
    // reset to 0
    aiger_add_reset(aig, lit, 0);
  }

  // Add AND gates
  for(literalt::var_not i = 0; i < netlist.number_of_nodes(); i++)
  {
    const auto &node = netlist.nodes[i];
    if(node.is_and())
    {
      unsigned lhs = to_aiger_lit(literalt{i, false});
      unsigned rhs0 = to_aiger_lit(node.a);
      unsigned rhs1 = to_aiger_lit(node.b);
      aiger_add_and(aig, lhs, rhs0, rhs1);
    }
  }

  // Add constraints
  for(auto l : netlist.transition)
  {
    unsigned lit = to_aiger_lit(l);
    aiger_add_constraint(aig, lit, nullptr);
  }

  // Write in ASCII mode to the stream
  auto put_fn = [](char ch, void *s) -> int
  {
    auto *os = static_cast<std::ostream *>(s);
    os->put(ch);
    return os->good() ? static_cast<unsigned char>(ch) : EOF;
  };

  aiger_write_generic(aig, aiger_ascii_mode, &out, put_fn);

  aiger_reset(aig);
}
