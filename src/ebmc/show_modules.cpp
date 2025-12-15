/*******************************************************************\

Module: Show Modules

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "show_modules.h"

#include <util/json_irep.h>
#include <util/symbol_table_base.h>
#include <util/xml_irep.h>

void show_modulest::xml(std::ostream &out) const
{
  std::size_t count = 0;

  for(const auto &module : modules)
  {
    count++;

    xmlt xml("module");
    xml.new_element("number").data = std::to_string(count); // will go away
    xml.set_attribute("number", std::to_string(count));

    xmlt &l = xml.new_element();
    convert(module.source_location, l);
    l.name = "location";

    // these go away
    xml.new_element("identifier").data = id2string(module.identifier);
    xml.new_element("mode").data = id2string(module.mode);
    xml.new_element("name").data = id2string(module.display_name);

    // these stay
    xml.set_attribute("identifier", id2string(module.identifier));
    xml.set_attribute("mode", id2string(module.mode));
    xml.set_attribute("name", id2string(module.display_name));

    out << xml;
  }
}

void show_modulest::plain_text(std::ostream &out) const
{
  std::size_t count = 0;

  for(const auto &module : modules)
  {
    count++;

    out << "Module " << count << ":" << '\n';

    out << "  Location:   " << module.source_location << '\n';
    out << "  Mode:       " << module.mode << '\n';
    out << "  Identifier: " << module.identifier << '\n';
    out << "  Name:       " << module.display_name << '\n' << '\n';
  }
}

void show_modulest::json(std::ostream &out) const
{
  json_arrayt json_modules;

  for(const auto &module : modules)
  {
    json_objectt json_module;
    json_module["location"] = ::json(module.source_location);
    json_module["identifier"] = json_stringt{id2string(module.identifier)};
    json_module["mode"] = json_stringt{id2string(module.mode)};
    json_module["name"] = json_stringt{id2string(module.display_name)};

    json_modules.push_back(std::move(json_module));
  }

  out << json_modules;
}

show_modulest
show_modulest::from_symbol_table(const symbol_table_baset &symbol_table)
{
  show_modulest show_modules;

  for(const auto &s : symbol_table.symbols)
  {
    const symbolt &symbol = s.second;

    if(symbol.type.id() == ID_module)
    {
      show_modules.modules.emplace_back(
        symbol.name, symbol.display_name(), symbol.mode, symbol.location);
    }
  }

  return show_modules;
}
