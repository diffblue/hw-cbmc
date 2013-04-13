/*******************************************************************\

Module: CEGAR for BMC

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/i2string.h>

#include <solvers/sat/satcheck.h>

#include "bmc_cegar.h"

/*******************************************************************\

Function: bmc_cegart::verify

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool bmc_cegart::verify(unsigned bound)
{
  message.status("Checking Abstract Model (bound="+
                 i2string(bound)+")");

  satcheckt satcheck;
  cnft &solver=satcheck;

  unwind(bound, abstract_netlist, solver);
  
  if(verbose)
    message.status("Running "+solver.solver_text());

  switch(solver.prop_solve())
  {
  case propt::P_SATISFIABLE:
    if(verbose)
      message.status("SAT: bug found within bound");
    break;

  case propt::P_UNSATISFIABLE:
    if(verbose)
      message.status("UNSAT: No bug found within bound");
    return true;

  case propt::P_ERROR:
    std::cerr << "Error from SAT solver\n";
    throw 0;

  default:
    std::cerr << "Unexpected result from SAT solver\n";
    throw 0;
  }
  
  return false;
}
