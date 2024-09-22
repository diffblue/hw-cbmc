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
  message.status() << "Simulating Counterexample" << messaget::eom;

  satcheckt satcheck{message.get_message_handler()};
  cnft &solver=satcheck;

  unwind(bound, concrete_netlist, solver);

  message.status() << "Running " << solver.solver_text() << messaget::eom;

  switch(solver.prop_solve())
  {
  case propt::resultt::P_SATISFIABLE:
    message.status() << "SAT: bug found within bound" << messaget::eom;

    show_counterexample(
      properties, prop_bv, message.get_message_handler(), solver, bmc_map, ns);
    return true;

  case propt::resultt::P_UNSATISFIABLE:
    message.status() << "UNSAT: No bug found within bound" << messaget::eom;
    break;

  case propt::resultt::P_ERROR:
    message.error() << "Error from SAT solver" << messaget::eom;
    throw 0;

  default:
    message.error() << "Unexpected result from SAT solver" << messaget::eom;
    throw 0;
  }
  
  return false;
}
