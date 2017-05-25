/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <cbmc/bv_cbmc.h>
#include <trans-word-level/unwind.h>
#include <trans-word-level/trans_trace_word_level.h>

#include "hw_bmc.h"

/*******************************************************************\

Function: hw_bmct::do_unwind_module

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void hw_bmct::do_unwind_module()
{
  if(unwind_module=="" ||
     unwind_no_timeframes==0) return;
  
  const symbolt &symbol=ns.lookup(unwind_module);

  status() << "Unwinding transition system `" << symbol.name
           << "' with " << unwind_no_timeframes
           << " time frames" << eom;

  ::unwind(
    to_trans_expr(symbol.value),
    *this,    // message
    prop_conv,
    unwind_no_timeframes,
    ns,
    true);

  status() << "Unwinding transition system done" << eom;

}

/*******************************************************************\

Function: hw_bmct::show_unwind_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void hw_bmct::show_unwind_trace()
{
  if(unwind_module=="" ||
     unwind_no_timeframes==0) return;
     
  trans_tracet trans_trace;
  
  compute_trans_trace(
    prop_conv,
    unwind_no_timeframes,
    ns,
    unwind_module,
    trans_trace);

  if(options.get_option("vcd")!="")
  {
    if(options.get_option("vcd")=="-")
      show_trans_trace_vcd(
        trans_trace,
        *this, // message
        ns,
        std::cout);
    else
    {
      std::ofstream out(options.get_option("vcd").c_str());
      show_trans_trace_vcd(
        trans_trace,
        *this, // message
        ns,
        out);
    }
  }

  show_trans_trace(
    trans_trace,
    *this, // message
    ns,
    ui);
}
