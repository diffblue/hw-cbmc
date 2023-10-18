/*******************************************************************\

Module: CEGAR for BMC: Simulation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <solvers/sat/satcheck.h>
#include <trans-netlist/counterexample_netlist.h>

#include "bmc_cegar.h"

/*******************************************************************\

Function: bmc_cegart::simulate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool bmc_cegart::simulate(std::size_t bound)
{
  status() << "Simulating Counterexample" << eom;

  satcheckt satcheck{*message_handler};
  cnft &solver=satcheck;

  unwind(bound, concrete_netlist, solver);
  
  status() << "Running " << solver.solver_text() << eom;
    
  switch(solver.prop_solve())
  {
  case propt::resultt::P_SATISFIABLE:
    status() << "SAT: bug found within bound" << eom;
    return true;

  case propt::resultt::P_UNSATISFIABLE:
    status() << "UNSAT: No bug found within bound" << eom;
    break;

  case propt::resultt::P_ERROR:
    error() << "Error from SAT solver" << eom;
    throw 0;

  default:
    error() << "Unexpected result from SAT solver" << eom;
    throw 0;
  }
  
  return false;
}
