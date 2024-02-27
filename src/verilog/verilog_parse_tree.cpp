/*******************************************************************\

Module: Verilog Parser

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_parse_tree.h"
#include "verilog_typecheck_base.h"

/*******************************************************************\

Function: verilog_parse_treet::create_class

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_parse_treet::create_class(exprt &name)
{
  items.emplace_back(itemt::CLASS);
  itemt &item = items.back();
  item.source_location = name.source_location();
}

/*******************************************************************\

Function: verilog_parse_treet::create_interface

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_parse_treet::create_interface(exprt &name)
{
  items.emplace_back(itemt::INTERFACE);
  itemt &item = items.back();
  item.source_location = name.source_location();
}

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
  items.emplace_back(itemt::MODULE);
  itemt &item=items.back();

  verilog_modulet &new_module=item.verilog_module;

  if(ports.get_sub().size()==1 &&
     ports.get_sub().front().is_nil())
    ports.clear();

  new_module.name=name.id();
  new_module.parameter_port_list.swap(parameter_port_list);
  new_module.ports.swap(ports);
  new_module.location=((const exprt &)module_keyword).source_location();
  new_module.module_items.swap(module_items);

  // add to module map  
  module_map[new_module.name]=--items.end();
}

/*******************************************************************\

Function: verilog_parse_treet::create_package

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_parse_treet::create_package(exprt &name)
{
  items.emplace_back(itemt::PACKAGE);
  itemt &item = items.back();
  item.source_location = name.source_location();
}

/*******************************************************************\

Function: verilog_parse_treet::create_primitive

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_parse_treet::create_primitive(exprt &name)
{
  items.emplace_back(itemt::PRIMITIVE);
  itemt &item = items.back();
  item.source_location = name.source_location();
}

/*******************************************************************\

Function: verilog_parse_treet::create_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_parse_treet::create_program(exprt &name)
{
  items.emplace_back(itemt::PROGRAM);
  itemt &item = items.back();
  item.source_location = name.source_location();
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
        id2string(verilog_module_symbol(it->verilog_module.name)));
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
      module_map[it->verilog_module.name]=it;
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
  case itemt::CLASS:
    out << "CLASS " << source_location << "\n";
    break;

  case itemt::INTERFACE:
    out << "INTERFACE " << source_location << "\n";
    break;

  case itemt::MODULE:
    verilog_module.show(out);
    break;

  case itemt::PACKAGE:
    out << "PACKAGE " << source_location << "\n";
    break;

  case itemt::PRIMITIVE:
    out << "PRIMITIVE " << source_location << "\n";
    break;

  case itemt::PROGRAM:
    out << "PROGRAM " << source_location << "\n";
    break;

  case itemt::TYPEDEF:
    verilog_typedef.show(out);
    break;
    
  default:
    PRECONDITION(false);
  }
}
