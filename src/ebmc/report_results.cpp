/*******************************************************************\

Module: Result Reporting

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Result Reporting

#include "report_results.h"

#include <util/json.h>
#include <util/xml.h>

#include "ebmc_error.h"
#include "output_file.h"
#include "waveform.h"

#include <iostream>

/*******************************************************************\

Function: ebmc_baset::report_results

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void report_results(
  const cmdlinet &cmdline,
  bool show_proof_via,
  const property_checker_resultt &result,
  const namespacet &ns,
  message_handlert &message_handler)
{
  if(cmdline.isset("json-result"))
  {
    auto filename = cmdline.get_value("json-result");
    auto outfile = output_filet{filename};

    json_objectt json_results;
    auto &json_properties = json_results["properties"].make_array();

    for(const auto &property : result.properties)
    {
      if(property.is_disabled())
        continue;

      json_objectt json_property;
      json_property["identifier"] =
        json_stringt(id2string(property.identifier));
      json_property["status"] = json_stringt(property.status_as_string());

      if(property.has_witness_trace())
        json_property["trace"] = json(property.witness_trace.value(), ns);

      if(property.is_proved() && property.proof_via.has_value())
        json_property["proof_via"] = json_stringt{property.proof_via.value()};

      json_properties.push_back(std::move(json_property));
    }

    outfile.stream() << json_results;
  }

  if(
    static_cast<ui_message_handlert &>(message_handler).get_ui() ==
    ui_message_handlert::uit::XML_UI)
  {
    for(const auto &property : result.properties)
    {
      if(property.is_disabled())
        continue;

      xmlt xml_result("result");
      xml_result.set_attribute("property", id2string(property.identifier));
      xml_result.set_attribute("status", property.status_as_string());

      if(property.has_witness_trace())
        xml_result.new_element() = xml(property.witness_trace.value(), ns);

      if(property.is_proved() && property.proof_via.has_value())
        xml_result.set_attribute("proof_via", property.proof_via.value());

      std::cout << xml_result << '\n' << std::flush;
    }
  }
  else
  {
    messaget message(message_handler);
    message.status() << messaget::eom;
    message.status() << "** Results:" << messaget::eom;

    for(const auto &property : result.properties)
    {
      if(property.is_disabled())
        continue;

      message.result() << "[" << property.name << "] " << property.description
                       << ": ";

      using statust = ebmc_propertiest::propertyt::statust;

      switch(property.status)
      {
      // clang-format off
      case statust::ASSUMED: message.result() << messaget::blue; break;
      case statust::PROVED: message.result() << messaget::green; break;
      case statust::PROVED_WITH_BOUND: message.result() << messaget::green; break;
      case statust::REFUTED: message.result() << messaget::bright_red; break;
      case statust::REFUTED_WITH_BOUND: message.result() << messaget::bright_red; break;
      case statust::DROPPED: message.result() << messaget::red; break;
      case statust::FAILURE: message.result() << messaget::red; break;
      case statust::UNKNOWN: message.result() << messaget::yellow; break;
      case statust::UNSUPPORTED: message.result() << messaget::yellow; break;
      case statust::DISABLED: break;
      case statust::INCONCLUSIVE: message.result() << messaget::yellow; break;
      }
      // clang-format on

      message.result() << property.status_as_string();

      message.result() << messaget::reset;

      if(
        show_proof_via && property.is_proved() &&
        property.proof_via.has_value())
      {
        message.result() << " (" << property.proof_via.value() << ')';
      }

      message.result() << messaget::eom;

      if(property.has_witness_trace())
      {
        auto term = [&property]() {
          return property.is_exists_path() ? "Trace" : "Counterexample";
        };

        if(cmdline.isset("trace"))
        {
          message.result() << term() << ":\n" << messaget::eom;
          show_trans_trace(
            property.witness_trace.value(), message, ns, std::cout);
        }
        else if(cmdline.isset("numbered-trace"))
        {
          message.result() << term();
          auto failing_opt =
            property.witness_trace->get_min_failing_timeframe();
          if(failing_opt.has_value())
          {
            if(*failing_opt == 0)
              message.result() << " with 1 state";
            else
              message.result() << " with " << *failing_opt + 1 << " states";
          }
          message.result() << ':' << messaget::eom;
          show_trans_trace_numbered(
            property.witness_trace.value(), message, ns, std::cout);
        }
        else if(cmdline.isset("waveform"))
        {
          message.result() << term() << ":" << messaget::eom;
          show_waveform(property.witness_trace.value(), ns);
        }
      }
    }
  }

  if(cmdline.isset("vcd"))
  {
    const auto outfile_prefix = cmdline.get_value("vcd") + '.';
    for(const auto &property : result.properties)
    {
      if(property.has_witness_trace())
      {
        const auto filename =
          outfile_prefix + id2string(property.name) + "_witness.vcd";
        auto outfile = output_filet{filename};
        messaget message(message_handler);
        message.status() << "Writing witness trace VCD file to " << filename
                         << messaget::eom;
        show_trans_trace_vcd(
          property.witness_trace.value(), message, ns, outfile.stream());
      }
    }
  }
}
