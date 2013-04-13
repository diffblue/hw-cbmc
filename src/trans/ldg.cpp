/*******************************************************************\

Module: Latch Dependency Graph

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>
#include <cassert>

#include "ldg.h"

/*******************************************************************\

Function: ldgt::compute

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ldgt::compute(const netlistt &netlist)
{
  compute(netlist, netlist.var_map.latches);
}

/*******************************************************************\

Function: ldgt::compute

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ldgt::compute(
  const netlistt &netlist,
  const latchest &localization)
{
  latches=netlist.var_map.latches;
  
  // we start with a node for each variable
  nodes.clear();
  nodes.resize(netlist.nodes.size());
  
  for(latchest::const_iterator
      l_it=localization.begin();
      l_it!=localization.end();
      l_it++)
    nodes[*l_it].is_source_latch=true;

  // get the next state nodes
    
  for(var_mapt::mapt::const_iterator
      m_it=netlist.var_map.map.begin();
      m_it!=netlist.var_map.map.end();
      m_it++)
  {
    const var_mapt::vart &var=m_it->second;
    if(var.is_latch())
    {
      for(unsigned bit_nr=0; bit_nr<var.bits.size(); bit_nr++)
      {
        const var_mapt::vart::bitt &bit=var.bits[bit_nr];
        nodes[bit.current.var_no()].next_state=bit.next;
      }
    }
  }
  
  aigt::terminalst terminals;
  netlist.get_terminals(terminals);

  for(latchest::const_iterator
      l_it=localization.begin();
      l_it!=localization.end();
      l_it++)
  {
    unsigned v=*l_it;
    literalt next_state=nodes[v].next_state;
    const aigt::terminal_sett &t=terminals[next_state.var_no()];

    for(std::set<unsigned>::const_iterator
        it=t.begin(); it!=t.end(); it++)
    {
      unsigned v2=*it;
      if(nodes[v2].is_source_latch)
      {
        add_edge(v2, v);
        #if 0
        std::cout << "DEP: " << v2 << " -> " << v << std::endl;
        #endif
      }
    }
  }
}
