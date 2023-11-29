/*******************************************************************\

Module: VHDL Parser

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include "vhdl_parse_tree.h"

/*******************************************************************\

Function: vhdl_parse_treet::create_module

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
void vhdl_parse_treet::create_module(
  irept &attributes,
  irept &module_keyword,
  exprt &name,
  exprt &ports,
  exprt &module_items)
{
  items.push_back(itemt());
  itemt &item=items.back();
  
  item.type=itemt::MODULE;

  vhdl_modulet &new_module=item.vhdl_module;

  if(ports.get_sub().size()==1 &&
     ports.get_sub().front().is_nil())
    ports.clear();

  new_module.name=name.id();
  new_module.ports.swap(ports);
  new_module.location=((exprt &)module_keyword).location();
  new_module.module_items.swap(module_items);

  // add to module map  
  module_map[new_module.name]=--items.end();
}
#endif

/*******************************************************************\

Function: vhdl_parse_treet::modules_provided

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
void vhdl_parse_treet::modules_provided(
  std::set<std::string> &module_set) const
{
  for(itemst::const_iterator it=items.begin();
      it!=items.end();
      it++)
    if(it->is_module())
      module_set.insert(
        id2string(vhdl_module_symbol(it->vhdl_module.name)));
}
#endif

/*******************************************************************\

Function: vhdl_parse_treet::build_module_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
void vhdl_parse_treet::build_module_map()
{
  module_map.clear();

  for(itemst::iterator it=items.begin();
      it!=items.end();
      it++)
    if(it->is_module())
      module_map[it->vhdl_module.name]=it;
}
#endif

/*******************************************************************\

Function: vhdl_parse_treet::show

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_parse_treet::show(std::ostream &out) const
{
  for(itemst::const_iterator it=items.begin();
      it!=items.end();
      it++)
    it->show(out);
}

/*******************************************************************\

Function: vhdl_parse_treet::itemt::show

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_parse_treet::itemt::show(std::ostream &out) const
{
  irep_idt type=get_item_type();
  
  if(type=="architecture")
  {
    out << "ARCHITECTURE " << pretty_name(get_name());
    out << '\n';
  }
  else if(type=="entity")
  {
    out << "ENTITY " << pretty_name(get_name());
    out << '\n';
  }
  else if(type=="use")
  {
    out << "USE ";
    out << '\n';
  }
  else if(type=="library")
  {
    out << "LIBRARY ";
    out << '\n';
  }
  else if(type=="package")
  {
    out << "PACKAGE " << pretty_name(get_name());
    out << '\n';
  }
  else
    DATA_INVARIANT(false, "unknown item type");
}

/*******************************************************************\

Function: vhdl_parse_treet::itemt::pretty_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string vhdl_parse_treet::itemt::pretty_name(const irept &name)
{
  if(name.id()==ID_symbol)
    return name.get_string(ID_identifier);
  else
    return "?";
}
