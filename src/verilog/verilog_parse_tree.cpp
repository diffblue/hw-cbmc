/*******************************************************************\

Module: Verilog Parser

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_parse_tree.h"
#include "verilog_typecheck_base.h"

/*******************************************************************\

Function: verilog_parse_treet::create_module

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_parse_treet::create_module(
  irept &attributes,
  irept &module_keyword,
  exprt &name,
  exprt &parameter_port_list,
  exprt &ports,
  exprt &module_items)
{
  if(ports.get_sub().size()==1 &&
     ports.get_sub().front().is_nil())
    ports.clear();

  verilog_module_sourcet new_module{name.id()};

  new_module.add(ID_parameter_port_list) = std::move(parameter_port_list);
  new_module.add(ID_ports) = std::move(ports);
  new_module.add_source_location() =
    ((const exprt &)module_keyword).source_location();
  new_module.add(ID_module_items) = std::move(module_items);

  auto &new_item = add_item(std::move(new_module));

  // add to module map
  module_map[name.id()] = &to_verilog_module_source(new_item);
}

/*******************************************************************\

Function: verilog_parse_treet::modules_provided

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_parse_treet::modules_provided(
  std::set<std::string> &module_set) const
{
  for(auto &item : items)
  {
    if(item.id() == ID_verilog_module)
      module_set.insert(id2string(
        verilog_module_symbol(to_verilog_module_source(item).base_name())));
  }
}

/*******************************************************************\

Function: verilog_parse_treet::build_module_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_parse_treet::build_module_map()
{
  module_map.clear();

  for(const auto &item : items)
  {
    if(item.id() == ID_verilog_module)
    {
      auto &verilog_module = to_verilog_module_source(item);
      module_map[verilog_module.base_name()] = &verilog_module;
    }
  }
}

/*******************************************************************\

Function: verilog_parse_treet::show

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_parse_treet::show(std::ostream &out) const
{
  for(const auto &item : items)
    show(item, out);
}

/*******************************************************************\

Function: verilog_parse_treet::show

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_parse_treet::show(const itemt &item, std::ostream &out) const
{
  if(item.id() == ID_verilog_module)
    to_verilog_module_source(item).show(out);
  else
    out << item.pretty() << '\n';
}
