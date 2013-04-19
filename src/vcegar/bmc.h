/*******************************************************************\

Module: Basic BMC

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VCEGAR_BMC_H
#define CPROVER_VCEGAR_BMC_H

#include <ebmc/ebmc_base.h>

class bmct:public ebmc_baset
{
public:
  explicit bmct(cmdlinet &_cmdline):ebmc_baset(_cmdline)
  {
  }

  int do_sat();
};

#endif
