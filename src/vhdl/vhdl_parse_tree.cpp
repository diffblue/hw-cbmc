/*******************************************************************\

Module: VHDL Parser

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "vhdl_parse_tree.h"

#include <algorithm>
#include <ostream>

/*******************************************************************\

Function: vhdl_parse_treet::show

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_parse_treet::show(std::ostream &out) const
{
  for(itemst::const_iterator it = items.begin(); it != items.end(); it++)
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
  irep_idt type = get_item_type();

  if(type == "architecture")
  {
    out << "ARCHITECTURE " << pretty_name(get_name()) << " OF "
        << pretty_name(find(ID_entity));
    out << '\n';
  }
  else if(type == "entity")
  {
    out << "ENTITY " << pretty_name(get_name());
    out << '\n';
  }
  else if(type == "use")
  {
    out << "USE ";
    out << '\n';
  }
  else if(type == "library")
  {
    out << "LIBRARY ";
    out << '\n';
  }
  else if(type == "package")
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
  if(name.id() == ID_symbol)
    return name.get_string(ID_identifier);
  else
    return "?";
}

/*******************************************************************\

Function: vhdl_parse_treet::itemt::to_lower

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt vhdl_parse_treet::itemt::to_lower(const irep_idt &src)
{
  std::string data = id2string(src);

  // extended identifiers, \...\, are case sensitive (IEEE 1076-2008 15.4.3)
  if(!data.empty() && data[0] == '\\')
    return src;

  std::transform(data.begin(), data.end(), data.begin(), ::tolower);
  return data;
}
