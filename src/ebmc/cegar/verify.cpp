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

bool bmc_cegart::verify(const std::size_t bound)
{
  status() << "Checking abstract model (bound=" << bound << ")" << eom;

  satcheckt satcheck{*message_handler};
  cnft &solver=satcheck;

  unwind(bound, abstract_netlist, solver);
  
  status() << "Running " << solver.solver_text() << eom;

  switch(solver.prop_solve())
  {
  case propt::resultt::P_SATISFIABLE:
    status() << "SAT: bug found within bound" << eom;
    break;

  case propt::resultt::P_UNSATISFIABLE:
    status() << "UNSAT: No bug found within bound" << eom;
    return true;

  case propt::resultt::P_ERROR:
    error() << "Error from SAT solver" << eom;
    throw 0;

  default:
    error() << "Unexpected result from SAT solver" << eom;
    throw 0;
  }
  
  return false;
}
