/*******************************************************************\

Module: Base for Verification Modules

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/xml.h>
#include <util/xml_expr.h>
#include <util/i2string.h>
#include <util/xml_irep.h>

#include "ebmc_base.h"

/*******************************************************************\

Function: ebmc_baset::show_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ebmc_baset::show_properties()
{
  unsigned p_nr=1;

  for(const auto & p : properties)
  {
    switch(get_ui())
    {
    case ui_message_handlert::XML_UI:
      {
        xmlt xml("property");
        xml.set_attribute("name", id2string(p.name));
        
        xml.new_element("number").data=i2string(p_nr); // will go away
        xml.new_element("expression").data=p.expr_string;
        xml.new_element("description").data=p.description;

        if(p.location.is_not_nil())
          xml.new_element("location")=::xml(p.location);

        std::cout << xml << '\n';
      }
      break;
  
    case ui_message_handlert::PLAIN:
      std::cout << p.name << ": ";
      std::cout << p.expr_string;
      if(!p.description.empty())
        std::cout << " (" << p.description << ")";
      std::cout << '\n';
      break;

    default:;
    }
    
    p_nr++;
  }
}
