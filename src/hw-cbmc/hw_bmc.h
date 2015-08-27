/*******************************************************************\

Module: Bounded Model Checking for ANSI-C + HDL

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_HW_CBMC_BMC_H
#define CPROVER_HW_CBMC_BMC_H

#include <cbmc/bmc.h>

class hw_bmct:public bmct
{
public:
  hw_bmct(
    const optionst &_options,
    const symbol_tablet &_symbol_table,
    message_handlert &_message_handler,
    prop_convt &_prop_conv):
    bmct(_options, _symbol_table, _message_handler, _prop_conv)
  {
  }

  irep_idt unwind_module;
  unsigned unwind_no_timeframes;

  virtual void do_unwind_module(
    decision_proceduret &decision_procedure);

  virtual void show_unwind_trace();
    
  virtual void error_trace()
  {
    bmct::error_trace();
    show_unwind_trace();
  }
};

#endif
