/*******************************************************************\

Module: Result Reporting

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Result Reporting

#include "report_results.h"

#include <util/json.h>
#include <util/unicode.h>
#include <util/xml.h>

#include "ebmc_error.h"
#include "waveform.h"

#include <fstream>
#include <iostream>

/*******************************************************************\

Function: ebmc_baset::report_results

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void report_results(
  const cmdlinet &cmdline,
  const ebmc_propertiest &properties,
  const namespacet &ns,
  message_handlert &message_handler)
{
  if(cmdline.isset("json-result"))
  {
    auto filename = cmdline.get_value("json-result");
    std::ofstream out(widen_if_needed(filename));
    if(!out)
      throw ebmc_errort() << "failed to open " << filename;

    json_objectt json_results;
    auto &json_properties = json_results["properties"].make_array();

    for(const auto &property : properties.properties)
    {
      if(property.is_disabled())
        continue;

      json_objectt json_property;
      json_property["identifier"] = json_stringt(id2string(property.name));

      json_property["status"] = json_stringt(
        [&property]()
        {
          using statust = ebmc_propertiest::propertyt::statust;

          switch(property.status)
          {
          case statust::SUCCESS:
            return "HOLDS";
          case statust::FAILURE:
            return "REFUTED";
          case statust::UNKNOWN:
            return "UNKNOWN";
          case statust::DISABLED:
          default:
            UNREACHABLE;
          }
        }());

      if(property.is_failure())
        json_property["counterexample"] = json(property.counterexample, ns);

      json_properties.push_back(std::move(json_property));
    }

    out << json_results;
  }

  if(
    static_cast<ui_message_handlert &>(message_handler).get_ui() ==
    ui_message_handlert::uit::XML_UI)
  {
    for(const auto &property : properties.properties)
    {
      if(property.is_disabled())
        continue;

      xmlt xml_result("result");
      xml_result.set_attribute("property", id2string(property.name));

      using statust = ebmc_propertiest::propertyt::statust;

      switch(property.status)
      {
      case statust::SUCCESS:
        xml_result.set_attribute("status", "SUCCESS");
        break;
      case statust::FAILURE:
        xml_result.set_attribute("status", "FAILURE");
        break;
      case statust::UNKNOWN:
        xml_result.set_attribute("status", "UNKNOWN");
        break;
      case statust::DISABLED:;
      }

      if(property.is_failure())
        xml_result.new_element() = xml(property.counterexample, ns);

      std::cout << xml_result << '\n' << std::flush;
    }
  }
  else
  {
    messaget message(message_handler);
    message.status() << messaget::eom;
    message.status() << "** Results:" << messaget::eom;

    for(const auto &property : properties.properties)
    {
      if(property.is_disabled())
        continue;

      message.status() << "[" << property.name << "] " << property.expr_string
                       << ": ";

      switch(property.status)
      {
      case ebmc_propertiest::propertyt::statust::SUCCESS:
        message.status() << "SUCCESS";
        break;
      case ebmc_propertiest::propertyt::statust::FAILURE:
        message.status() << "FAILURE";
        break;
      case ebmc_propertiest::propertyt::statust::UNKNOWN:
        message.status() << "UNKNOWN";
        break;
      case ebmc_propertiest::propertyt::statust::DISABLED:;
      }

      message.status() << messaget::eom;

      if(property.is_failure())
      {
        if(cmdline.isset("trace"))
        {
          message.status() << "Counterexample:\n" << messaget::eom;
          show_trans_trace(property.counterexample, message, ns, std::cout);
        }
        else if(cmdline.isset("waveform"))
        {
          message.status() << "Counterexample:" << messaget::eom;
          show_waveform(property.counterexample, ns);
        }
      }
    }
  }

  if(cmdline.isset("vcd"))
  {
    for(const auto &property : properties.properties)
    {
      if(property.is_failure())
      {
        std::string vcdfile = cmdline.get_value("vcd");
        std::ofstream vcd(widen_if_needed(vcdfile));

        messaget message(message_handler);
        show_trans_trace_vcd(property.counterexample, message, ns, vcd);

        break;
      }
    }
  }
}
