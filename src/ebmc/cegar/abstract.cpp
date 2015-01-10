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
  message.status() << "Abstracting" << messaget::eom;

  if(initial_abstraction)
  {
    initial_abstraction=false;
    abstract_netlist=concrete_netlist;
    
    if(verbose) message.status() << "Computing concrete LDG" << messaget::eom;
   
    ldgt ldg;
 
    ldg.compute(concrete_netlist);

    if(verbose) message.status() << "Computing ordering" << messaget::eom;
    
    latch_orderingt latch_ordering;
    latch_ordering.compute(ldg);

    for(unsigned l=0; l<latch_ordering.node_ordering.size(); l++)
      std::cout << "Latch " << l << ": "
                << latch_ordering.node_ordering[l] << std::endl;

    exit(0);
  }
}
