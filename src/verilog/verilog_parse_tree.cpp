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
  items.push_back(itemt(itemt::MODULE));

  if(ports.get_sub().size()==1 &&
     ports.get_sub().front().is_nil())
    ports.clear();

  verilog_module_sourcet new_module{name.id()};

  new_module.add(ID_parameter_port_list) = std::move(parameter_port_list);
  new_module.add(ID_ports) = std::move(ports);
  new_module.add_source_location() =
    ((const exprt &)module_keyword).source_location();
  new_module.add(ID_module_items) = std::move(module_items);

  items.back().verilog_module = std::move(new_module);

  // add to module map
  module_map[name.id()] = --items.end();
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
  for(itemst::const_iterator it=items.begin();
      it!=items.end();
      it++)
    if(it->is_module())
      module_set.insert(
        id2string(verilog_module_symbol(it->verilog_module.base_name())));
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

  for(itemst::iterator it=items.begin();
      it!=items.end();
      it++)
    if(it->is_module())
      module_map[it->verilog_module.base_name()] = it;
}

/*******************************************************************\

Function: verilog_parse_treet::show

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_parse_treet::show(std::ostream &out) const
{
  for(itemst::const_iterator it=items.begin();
      it!=items.end();
      it++)
    it->show(out);
}

/*******************************************************************\

Function: verilog_parse_treet::itemt::show

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_parse_treet::itemt::show(std::ostream &out) const
{
  switch(type)
  {
  case itemt::MODULE:
    verilog_module.show(out);
    break;

  case itemt::PACKAGE_ITEM:
    out << "Package item:\n";
    out << verilog_package_item.pretty() << '\n';
    break;
    
  default:
    PRECONDITION(false);
  }
}
