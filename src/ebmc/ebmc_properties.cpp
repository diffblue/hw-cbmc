/*******************************************************************\

Module: Data Structure for the Properties

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "ebmc_properties.h"

#include <langapi/language_util.h>

bool ebmc_propertiest::from_transition_system(
  const transition_systemt &transition_system,
  ebmc_propertiest &properties,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  for(auto it = transition_system.symbol_table.symbol_module_map.lower_bound(
        transition_system.main_symbol->name);
      it != transition_system.symbol_table.symbol_module_map.upper_bound(
              transition_system.main_symbol->name);
      it++)
  {
    namespacet ns(transition_system.symbol_table);
    const symbolt &symbol = ns.lookup(it->second);

    if(symbol.is_property)
    {
      try
      {
        std::string value_as_string = from_expr(ns, symbol.name, symbol.value);

        message.debug() << "Property: " << value_as_string << messaget::eom;

        properties.properties.push_back(propertyt());
        properties.properties.back().number = properties.properties.size() - 1;

        if(symbol.pretty_name.empty())
          properties.properties.back().name = symbol.name;
        else
          properties.properties.back().name = symbol.pretty_name;

        properties.properties.back().expr = symbol.value;
        properties.properties.back().location = symbol.location;
        properties.properties.back().expr_string = value_as_string;
        properties.properties.back().mode = symbol.mode;
        properties.properties.back().description =
          id2string(symbol.location.get_comment());
      }

      catch(const char *e)
      {
        message.error() << e << messaget::eom;
        return true;
      }

      catch(const std::string &e)
      {
        message.error() << e << messaget::eom;
        return true;
      }

      catch(int)
      {
        return true;
      }
    }
  }

  return false;
}
