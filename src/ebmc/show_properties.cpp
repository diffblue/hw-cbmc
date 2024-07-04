/*******************************************************************\

Module: Base for Verification Modules

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/json.h>
#include <util/json_irep.h>
#include <util/xml.h>
#include <util/xml_irep.h>

#include "ebmc_base.h"
#include "ebmc_error.h"
#include "output_file.h"

#include <iostream>

/*******************************************************************\

Function: ebmc_baset::show_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ebmc_baset::show_properties()
{
  unsigned p_nr=1;

  auto make_xml =
    [](const ebmc_propertiest::propertyt &p, std::size_t p_nr) -> xmlt {
    xmlt xml("property");
    xml.set_attribute("name", id2string(p.name));

    xml.new_element("number").data = std::to_string(p_nr); // will go away
    xml.new_element("description").data = p.description;

    if(p.location.is_not_nil())
      xml.new_element("location") = ::xml(p.location);

    return xml;
  };

  for(const auto &p : properties.properties)
  {
    switch(static_cast<ui_message_handlert &>(message.get_message_handler())
             .get_ui())
    {
    case ui_message_handlert::uit::XML_UI:
      std::cout << make_xml(p, p_nr) << '\n';
      break;
  
    case ui_message_handlert::uit::PLAIN:
      std::cout << p.name << ": " << p.description << '\n';
      break;

    case ui_message_handlert::uit::JSON_UI:
    default:;
    }

    p_nr++;
  }
}

/*******************************************************************\

Function: ebmc_baset::json_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ebmc_baset::json_properties(const std::string &file_name)
{
  json_arrayt json;

  for(const auto &p : properties.properties)
  {
    json_objectt json_property;
    json_property["identifier"] = json_stringt{id2string(p.identifier)};
    json_property["name"] = json_stringt{id2string(p.name)};
    json_property["description"] = json_stringt{p.description};

    if(p.location.is_not_nil())
      json_property["location"] = ::json(p.location);

    json.push_back(std::move(json_property));
  }

  auto outfile = output_filet{file_name};
  outfile.stream() << json;
}
