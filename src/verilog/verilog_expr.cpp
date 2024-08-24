/*******************************************************************\

Module: Verilog Expressions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_expr.h"

#include <util/prefix.h>

#include "verilog_typecheck_base.h"

typet verilog_declaratort::merged_type(const typet &declaration_type) const
{
  typet result = type();
  typet *p = &result;

  while(p->id() == ID_verilog_unpacked_array)
    p = &to_type_with_subtype(*p).subtype();

  DATA_INVARIANT(p->is_nil(), "merged_type only works on unpacked arrays");
  *p = declaration_type;

  return result;
}

bool function_call_exprt::is_system_function_call() const
{
  return function().id() == ID_symbol &&
         has_prefix(
           id2string(to_symbol_expr(function()).get_identifier()), "$");
}

void verilog_module_sourcet::show(std::ostream &out) const
{
  out << "Module: " << base_name() << '\n';

  out << "  Parameters:\n";

  for(auto &parameter : parameter_port_list())
    out << "    " << parameter.pretty() << '\n';

  out << '\n';

  out << "  Ports:\n";

  for(auto &port : ports())
    out << "    " << port.pretty() << '\n';

  out << '\n';

  out << "  Module items:\n";

  for(auto &item : module_items())
    out << "    " << item.pretty() << '\n';

  out << '\n';
}

static void submodules_rec(
  const verilog_module_itemt &module_item,
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

std::vector<irep_idt> verilog_module_sourcet::submodules() const
{
  std::vector<irep_idt> result;

  for(auto &item : module_items())
    submodules_rec(item, result);

  return result;
}
