/*******************************************************************\

Module: CEGAR for BMC

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

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
  message.status() << "Checking Abstract Model (bound="
                   << bound << ")" << messaget::eom;

  satcheckt satcheck;
  cnft &solver=satcheck;

  unwind(bound, abstract_netlist, solver);
  
  message.status() << "Running " << solver.solver_text() << messaget::eom;

  switch(solver.prop_solve())
  {
  case propt::P_SATISFIABLE:
    message.status() << "SAT: bug found within bound" << messaget::eom;
    break;

  case propt::P_UNSATISFIABLE:
    message.status() << "UNSAT: No bug found within bound" << messaget::eom;
    return true;

  case propt::P_ERROR:
    message.error() << "Error from SAT solver" << messaget::eom;
    throw 0;

  default:
    message.error() << "Unexpected result from SAT solver" << messaget::eom;
    throw 0;
  }
  
  return false;
}
