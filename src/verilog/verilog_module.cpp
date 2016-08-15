/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include "verilog_module.h"

/*******************************************************************\

Function: verilog_modulet::show

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_modulet::show(std::ostream &out) const
{
  out << "Module: " << name << '\n';

  out << "  Ports:\n";

  forall_irep(it, ports.get_sub())
    out << "    " << it->pretty() << '\n';

  out << std::endl;

  out << "  Module items:\n";

  forall_irep(it, module_items.get_sub())
    out << "    " << it->pretty() << '\n';

  out << '\n';
}
