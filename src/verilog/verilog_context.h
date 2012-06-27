/*******************************************************************\

Module: Verilog Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_CONTEXT_H
#define CPROVER_VERILOG_CONTEXT_H

#include <context.h>

/*******************************************************************\

   Class: verilog_contextt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class verilog_contextt
{
public:
  verilog_contextt(contextt &_context):context(_context)
  {
  }

protected:
  contextt &context;
  symbolt &context_lookup(const irep_idt &identifier);
};

#endif
