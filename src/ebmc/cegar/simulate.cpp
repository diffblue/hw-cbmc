/*******************************************************************\

Module: CEGAR for BMC: Simulation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>
#include <cassert>

#include <solvers/sat/satcheck.h>
#include <trans-netlist/counterexample.h>

#include "bmc_cegar.h"

/*******************************************************************\

Function: bmc_cegart::simulate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool bmc_cegart::simulate(unsigned bound)
{
  status() << "Simulating Counterexample" << eom;

  satcheckt satcheck;
  cnft &solver=satcheck;

  unwind(bound, concrete_netlist, solver);
  
  status() << "Running " << solver.solver_text() << eom;
    
  switch(solver.prop_solve())
  {
  case propt::P_SATISFIABLE:
    status() << "SAT: bug found within bound" << eom;

    show_counterexample(
      properties, prop_bv, get_message_handler(), solver, bmc_map,
      ns, ui_message_handlert::PLAIN);
    return true;

  case propt::P_UNSATISFIABLE:
    status() << "UNSAT: No bug found within bound" << eom;
    break;

  case propt::P_ERROR:
    error() << "Error from SAT solver" << eom;
    throw 0;

  default:
    error() << "Unexpected result from SAT solver" << eom;
    throw 0;
  }
  
  return false;
}
