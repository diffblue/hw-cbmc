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
  unsigned p=1;

  for(propertiest::const_iterator p_it=properties.begin();
      p_it!=properties.end();
      p_it++, p++)
  {
    switch(get_ui())
    {
    case ui_message_handlert::XML_UI:
      {
        xmlt xml("property");
        xml.set_attribute("name", id2string(p_it->name));
        
        xml.new_element("number").data=i2string(p);
        xml.new_element("expression").data=p_it->expr_string;
        xml.new_element("description").data=p_it->description;

        if(p_it->location.is_not_nil())
          xml.new_element("location")=::xml(p_it->location);

        std::cout << xml << '\n';
      }
      break;
  
    case ui_message_handlert::PLAIN:
      std::cout << p_it->name << ": " << p_it->expr_string
                << '\n';
      break;

    default:;
    }
  }
}
