/*******************************************************************\

Module: Basic BMC

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

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
  const namespacet ns(symbol_table);
  boolbvt boolbv(ns, satcheck);
  return do_ebmc(boolbv, false);
}
