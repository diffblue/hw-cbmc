/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <i2string.h>
#include <cbmc/bv_cbmc.h>
#include <trans/unwind.h>
#include <trans/trans_trace.h>

#include "hw_bmc.h"

/*******************************************************************\

Function: hw_bmct::do_unwind_module

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void hw_bmct::do_unwind_module(
  decision_proceduret &decision_procedure)
{
  if(unwind_module=="" ||
     unwind_no_timeframes==0) return;
  
  const symbolt &symbol=ns.lookup(unwind_module);

  status("Unwinding transition system "+id2string(symbol.name));

  //unsigned prev_no_clauses=prop.no_clauses();
  //unsigned prev_no_literals=prop.no_literals();

  ::unwind(
    to_trans_expr(symbol.value),
    *this,    // message
    decision_procedure,
    unwind_no_timeframes,
    ns,
    true);

  //print(7, "Clauses: "+i2string(prop.no_clauses()-prev_no_clauses)+" "+
  //         "Literals: "+i2string(prop.no_literals()-prev_no_literals)+
  //         "\n");
}

/*******************************************************************\

Function: hw_bmct::show_unwind_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void hw_bmct::show_unwind_trace(
  const prop_convt &prop_conv)
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
