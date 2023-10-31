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

  out << "  Parameters:\n";

  for(auto &parameter : parameter_port_list.get_sub())
    out << "    " << parameter.pretty() << '\n';

  out << '\n';

  out << "  Ports:\n";

  for(auto &port : ports.get_sub())
    out << "    " << port.pretty() << '\n';

  out << '\n';

  out << "  Module items:\n";

  for(auto &item : module_items.get_sub())
    out << "    " << item.pretty() << '\n';

  out << '\n';
}
