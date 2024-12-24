/*******************************************************************\

Module: CEGAR for BMC

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>
#include <cstdlib>

#include "bmc_cegar.h"

#include "latch_ordering.h"

/*******************************************************************\

Function: bmc_cegart::abstract

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmc_cegart::abstract()
{
  status() << "Abstracting" << eom;

  if(initial_abstraction)
  {
    initial_abstraction=false;
    abstract_netlist=concrete_netlist;
    
    status() << "Computing concrete LDG" << eom;
   
    ldgt ldg;
 
    ldg.compute(concrete_netlist);

    status() << "Computing ordering" << eom;
    
    latch_orderingt latch_ordering;
    latch_ordering.compute(ldg);

    for(std::size_t l = 0; l < latch_ordering.node_ordering.size(); l++)
      std::cout << "Latch " << l << ": " << latch_ordering.node_ordering[l]
                << std::endl;
  }
}
