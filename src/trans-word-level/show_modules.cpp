/*******************************************************************\

Module: Show Modules

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "show_modules.h"

#include <util/json_irep.h>
#include <util/xml_irep.h>

/*******************************************************************\

Function: show_modules_xml

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_modules_xml(const symbol_table_baset &symbol_table, std::ostream &out)
{
  std::size_t count = 0;

  for(const auto &s : symbol_table.symbols)
  {
    const symbolt &symbol = s.second;

    if(symbol.type.id() == ID_module)
    {
      count++;

      xmlt xml("module");
      xml.new_element("number").data = std::to_string(count); // will go away
      xml.set_attribute("number", std::to_string(count));

      xmlt &l = xml.new_element();
      convert(symbol.location, l);
      l.name = "location";

      // these go away
      xml.new_element("identifier").data = id2string(symbol.name);
      xml.new_element("mode").data = id2string(symbol.mode);
      xml.new_element("name").data = id2string(symbol.display_name());

      // these stay
      xml.set_attribute("identifier", id2string(symbol.name));
      xml.set_attribute("mode", id2string(symbol.mode));
      xml.set_attribute("name", id2string(symbol.display_name()));

      out << xml;
    }
  }
}

/*******************************************************************\

Function: show_modules

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_modules(const symbol_table_baset &symbol_table, std::ostream &out)
{
  std::size_t count = 0;

  for(const auto &s : symbol_table.symbols)
  {
    const symbolt &symbol=s.second;
  
    if(symbol.type.id()==ID_module)
    {
      count++;

      out << "Module " << count << ":" << '\n';

      out << "  Location:   " << symbol.location << '\n';
      out << "  Mode:       " << symbol.mode << '\n';
      out << "  Identifier: " << symbol.name << '\n';
      out << "  Name:       " << symbol.display_name() << '\n' << '\n';
    }
  }
}

/*******************************************************************\

Function: json_modules

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void json_modules(const symbol_table_baset &symbol_table, std::ostream &out)
{
  json_arrayt json_modules;

  for(const auto &s : symbol_table.symbols)
  {
    const symbolt &symbol = s.second;

    if(symbol.type.id() == ID_module)
    {
      json_objectt json_module;
      json_module["location"] = json(symbol.location);
      json_module["identifier"] = json_stringt{id2string(symbol.name)};
      json_module["mode"] = json_stringt{id2string(symbol.mode)};
      json_module["name"] = json_stringt{id2string(symbol.display_name())};

      json_modules.push_back(std::move(json_module));
    }
  }

  out << json_modules;
}
