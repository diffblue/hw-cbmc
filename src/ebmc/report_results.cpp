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
      json_property["status"] = json_stringt(property.status_as_string());

      if(property.has_counterexample())
        json_property["counterexample"] =
          json(property.counterexample.value(), ns);

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
      xml_result.set_attribute("status", property.status_as_string());

      if(property.has_counterexample())
        xml_result.new_element() = xml(property.counterexample.value(), ns);

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

      using statust = ebmc_propertiest::propertyt::statust;

      switch(property.status)
      {
      // clang-format off
      case statust::PROVED: message.status() << messaget::green; break;
      case statust::PROVED_WITH_BOUND: message.status() << messaget::green; break;
      case statust::REFUTED: message.status() << messaget::bright_red; break;
      case statust::DROPPED: message.status() << messaget::red; break;
      case statust::FAILURE: message.status() << messaget::red; break;
      case statust::UNKNOWN: message.status() << messaget::yellow; break;
      case statust::DISABLED: break;
      case statust::INCONCLUSIVE: message.status() << messaget::yellow; break;
      }
      // clang-format on

      message.status() << property.status_as_string();

      message.status() << messaget::reset << messaget::eom;

      if(property.has_counterexample())
      {
        if(cmdline.isset("trace"))
        {
          message.status() << "Counterexample:\n" << messaget::eom;
          show_trans_trace(
            property.counterexample.value(), message, ns, std::cout);
        }
        else if(cmdline.isset("numbered-trace"))
        {
          message.status() << "Counterexample:\n" << messaget::eom;
          show_trans_trace_numbered(
            property.counterexample.value(), message, ns, std::cout);
        }
        else if(cmdline.isset("waveform"))
        {
          message.status() << "Counterexample:" << messaget::eom;
          show_waveform(property.counterexample.value(), ns);
        }
      }
    }
  }

  if(cmdline.isset("vcd"))
  {
    for(const auto &property : properties.properties)
    {
      if(property.has_counterexample())
      {
        std::string vcdfile = cmdline.get_value("vcd");
        std::ofstream vcd(widen_if_needed(vcdfile));

        messaget message(message_handler);
        show_trans_trace_vcd(property.counterexample.value(), message, ns, vcd);

        break;
      }
    }
  }
}
