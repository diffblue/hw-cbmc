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
    const contextt &_context,
    message_handlert &_message_handler):
    bmct(_options, _context, _message_handler)
  {
  }

  irep_idt unwind_module;
  unsigned unwind_no_timeframes;

  virtual void do_unwind_module(
    decision_proceduret &decision_procedure);

  virtual void show_unwind_trace(
    const prop_convt &prop_conv);
    
  virtual void error_trace(const prop_convt &prop_conv)
  {
    bmct::error_trace(prop_conv);
    show_unwind_trace(prop_conv);
  }
};

#endif
