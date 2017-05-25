/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_HW_CBMC_PARSEOPTIONS_H
#define CPROVER_HW_CBMC_PARSEOPTIONS_H

#include <cbmc/cbmc_parse_options.h>

#define HW_CBMC_OPTIONS \
  "(showvarmap)(bound):(module):(top):" \
  "(show-modules)(gen-interface)(vcd):"

class hw_cbmc_parse_optionst:public cbmc_parse_optionst
{
public:
  virtual int doit();
  virtual void help();
  
  hw_cbmc_parse_optionst(int argc, const char **argv):
    cbmc_parse_optionst(argc, argv, HW_CBMC_OPTIONS)
  {
  }
  
protected:
  virtual int get_modules(expr_listt &bmc_constraints);

  irep_idt get_top_module();
  unsigned get_bound();
};

#endif
