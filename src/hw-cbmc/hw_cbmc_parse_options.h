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

  irep_idt unwind_module;
  unsigned unwind_no_timeframes;

  virtual void do_unwind_module(prop_convt &prop_conv);

  virtual void show_unwind_trace(const optionst &options,
                                 const prop_convt &prop_conv);

  virtual void error_trace(const optionst &options,
                           const prop_convt &prop_conv) {
    show_unwind_trace(options, prop_conv);
  }

protected:
  virtual int get_modules(std::list<exprt> &bmc_constraints);

  irep_idt get_top_module();
  unsigned get_bound();
};

#endif
