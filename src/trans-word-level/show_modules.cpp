/*******************************************************************\

Module: Show Modules

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <iostream>

#include <util/xml.h>
#include <util/xml_irep.h>

#include "show_modules.h"

/*******************************************************************\

Function: show_modules

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_modules(
  const symbol_tablet &symbol_table,
  ui_message_handlert::uit ui)
{
  unsigned count=0;

  forall_symbols(it, symbol_table.symbols)
  {
    const symbolt &symbol=it->second;
  
    if(symbol.type.id()==ID_module)
    {
      count++;

      switch(ui)
      {
      case ui_message_handlert::XML_UI:
        {
          xmlt xml("module");
          xml.new_element("number").data=std::to_string(count); // will go away
          xml.set_attribute("number", std::to_string(count));
        
          xmlt &l=xml.new_element();
          convert(symbol.location, l);
          l.name="location";
        
          // these go away
          xml.new_element("identifier").data=id2string(symbol.name);
          xml.new_element("mode").data=id2string(symbol.mode);
          xml.new_element("name").data=id2string(symbol.display_name());

          // these stay
          xml.set_attribute("identifier", id2string(symbol.name));
          xml.set_attribute("mode", id2string(symbol.mode));
          xml.set_attribute("name", id2string(symbol.display_name()));
          
          std::cout << xml << std::endl;
        }
  
        break;
      
      case ui_message_handlert::PLAIN:
        std::cout << "Module " << count << ":" << std::endl;

        std::cout << "  Location:   " << symbol.location << std::endl;
        std::cout << "  Mode:       " << symbol.mode << std::endl;
        std::cout << "  Identifier: " << symbol.name << std::endl;
        std::cout << "  Name:       " << symbol.display_name() << std::endl
                  << std::endl;
        break;
      
      default:
        assert(false);
      }
    }
  }
}
