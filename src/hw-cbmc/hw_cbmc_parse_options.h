/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_HW_CBMC_PARSEOPTIONS_H
#define CPROVER_HW_CBMC_PARSEOPTIONS_H

#include <cbmc/cbmc_parse_options.h>

#define HW_CBMC_OPTIONS \
  "(showvarmap)(bound):(module):(show-modules)(gen-interface)"

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
  virtual void register_languages();
  virtual bool get_modules(bmct &bmc);
};

#endif
