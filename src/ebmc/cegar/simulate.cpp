/*******************************************************************\

Module: CEGAR for BMC: Simulation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <solvers/sat/satcheck.h>
#include <trans/counterexample.h>

#include "bmc_cegar.h"

/*******************************************************************\

Function: bmc_cegart::simulate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool bmc_cegart::simulate(unsigned bound)
{
  message.status() << "Simulating Counterexample" << messaget::eom;

  satcheckt satcheck;
  cnft &solver=satcheck;

  unwind(bound, concrete_netlist, solver);
  
  if(verbose)
    message.status() << "Running " << solver.solver_text() << messaget::eom;
    
  switch(solver.prop_solve())
  {
  case propt::P_SATISFIABLE:
    if(verbose)
      message.status() << "SAT: bug found within bound" << messaget::eom;

    show_counterexample(properties, prop_bv, message, solver, bmc_map,
                        ns, ui_message_handlert::PLAIN);
    return true;

  case propt::P_UNSATISFIABLE:
    if(verbose)
      message.status() << "UNSAT: No bug found within bound" << messaget::eom;
    break;

  case propt::P_ERROR:
    std::cerr << "Error from SAT solver\n";
    throw 0;

  default:
    std::cerr << "Unexpected result from SAT solver\n";
    throw 0;
  }
  
  return false;
}
