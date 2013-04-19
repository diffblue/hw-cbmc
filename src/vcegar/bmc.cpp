/*******************************************************************\

Module: Basic BMC

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <i2string.h>

#include <solvers/flattening/boolbv.h>
#include <solvers/sat/satcheck.h>

#include "bmc.h"

/*******************************************************************\

Function: bmct::do_sat

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int bmct::do_sat()
{
  satcheckt satcheck;
  boolbvt boolbv(satcheck);
  return do_ebmc(boolbv, false);
}
