/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include "verilog_module.h"

#include "verilog_expr.h"
#include "verilog_typecheck_base.h"

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

/*******************************************************************\

Function: verilog_modulet::submodules_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_modulet::submodules_rec(
  const exprt &module_item,
  std::vector<irep_idt> &dest)
{
  if(module_item.id() == ID_inst)
  {
    dest.push_back(
      verilog_module_symbol(to_verilog_inst(module_item).get_module()));
  }
  else if(module_item.id() == ID_generate_block)
  {
    for(auto &sub_item : to_verilog_generate_block(module_item).module_items())
      submodules_rec(sub_item, dest);
  }
  else if(module_item.id() == ID_generate_if)
  {
    auto &generate_if = to_verilog_generate_if(module_item);
    submodules_rec(generate_if.then_case(), dest);
    if(generate_if.has_else_case())
      submodules_rec(generate_if.else_case(), dest);
  }
  else if(module_item.id() == ID_generate_for)
  {
    submodules_rec(to_verilog_generate_for(module_item).body(), dest);
  }
}

/*******************************************************************\

Function: verilog_modulet::submodules

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::vector<irep_idt> verilog_modulet::submodules() const
{
  std::vector<irep_idt> result;

  for(auto &item : module_items.get_sub())
    submodules_rec(static_cast<const exprt &>(item), result);

  return result;
}
