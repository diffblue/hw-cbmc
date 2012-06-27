/*******************************************************************\

Module: Variable Mapping HDL<->C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_GEN_INTERFACE_H
#define CPROVER_CBMC_GEN_INTERFACE_H

#include <iostream>

#include <context.h>

void gen_interface(
  contextt &context,
  const symbolt &module,
  bool have_bound,
  std::ostream &out,
  std::ostream &err);

#endif
