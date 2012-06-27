/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_module.h"

/*******************************************************************\

Function: verilog_modulet::show

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_modulet::show(std::ostream &out) const
{
  out << "Module: " << name << std::endl;

  out << "  Ports:" << std::endl;

  forall_irep(it, ports.get_sub())
    out << "    " << *it << std::endl;

  out << std::endl;

  out << "  Module items:" << std::endl;

  forall_irep(it, module_items.get_sub())
    out << "    " << *it << std::endl;

  out << std::endl;
}
