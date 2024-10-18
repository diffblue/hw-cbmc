/*******************************************************************\

Module: Data Structure for the Properties

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "ebmc_properties.h"

#include <langapi/language.h>
#include <langapi/language_util.h>
#include <langapi/mode.h>
#include <temporal-logic/normalize_property.h>
#include <verilog/sva_expr.h>

#include "ebmc_error.h"

std::string ebmc_propertiest::propertyt::status_as_string() const
{
  switch(status)
  {
  case statust::ASSUMED:
    return "ASSUMED";
  case statust::PROVED:
    return "PROVED";
  case statust::PROVED_WITH_BOUND:
    return "PROVED up to bound " + std::to_string(bound);
  case statust::REFUTED:
    return "REFUTED";
  case statust::REFUTED_WITH_BOUND:
    return "REFUTED up to bound " + std::to_string(bound);
  case statust::UNKNOWN:
    return "UNKNOWN";
  case statust::INCONCLUSIVE:
    return "INCONCLUSIVE";
  case statust::FAILURE:
    return failure_reason.has_value() ? "FAILURE: " + failure_reason.value()
                                      : "FAILURE";
  case statust::DROPPED:
    return "DROPPED";
  case statust::DISABLED:
  default:
    UNREACHABLE;
  }
}

ebmc_propertiest ebmc_propertiest::from_transition_system(
  const transition_systemt &transition_system,
  message_handlert &message_handler)
{
  messaget message(message_handler);
  ebmc_propertiest properties;

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
      std::string value_as_string = from_expr(ns, symbol.name, symbol.value);

      message.debug() << "Property: " << value_as_string << messaget::eom;

      properties.properties.push_back(propertyt());
      properties.properties.back().number = properties.properties.size() - 1;
      properties.properties.back().identifier = symbol.name;
      properties.properties.back().name = symbol.display_name();
      properties.properties.back().original_expr = symbol.value;
      properties.properties.back().location = symbol.location;
      properties.properties.back().mode = symbol.mode;
      properties.properties.back().description =
        id2string(symbol.location.get_comment());

      // Don't try to prove assumption properties.
      if(symbol.value.id() == ID_sva_assume)
      {
        properties.properties.back().status = propertyt::statust::ASSUMED;
        properties.properties.back().normalized_expr =
          normalize_property(to_sva_assume_expr(symbol.value).op());
      }
      else
      {
        properties.properties.back().normalized_expr =
          normalize_property(symbol.value);
      }

      message.debug() << "Normalized property: "
                      << from_expr(
                           ns,
                           symbol.name,
                           properties.properties.back().normalized_expr)
                      << messaget::eom;
    }
  }

  return properties;
}

bool ebmc_propertiest::select_property(
  const cmdlinet &cmdline,
  message_handlert &message_handler)
{
  if(cmdline.isset("property"))
  {
    std::string property = cmdline.get_value("property");

    // disable all assertions (not: assumptions)
    for(auto &p : properties)
      if(!p.is_assumed())
        p.status = propertyt::statust::DISABLED;

    bool found = false;

    for(auto &p : properties)
      if(p.name == property)
      {
        found = true;
        p.status = propertyt::statust::UNKNOWN;
        break;
      }

    if(!found)
    {
      messaget message(message_handler);
      message.error() << "Property " << property << " not found"
                      << messaget::eom;
      return true;
    }
  }

  return false;
}

ebmc_propertiest ebmc_propertiest::from_command_line(
  const cmdlinet &cmdline,
  const transition_systemt &transition_system,
  message_handlert &message_handler)
{
  // Property given as expression on command line?
  if(cmdline.isset('p'))
  {
    // NuSMV also uses -p
    namespacet ns(transition_system.symbol_table);

    auto language = get_language_from_mode(transition_system.main_symbol->mode);

    auto property_string = cmdline.get_value('p');

    exprt expr;
    if(language->to_expr(
         property_string,
         id2string(transition_system.main_symbol->module),
         expr,
         ns,
         message_handler))
    {
      throw ebmc_errort() << "failed to parse the given property expression";
    }

    // We give it an implict always, as in SVA

    if(expr.id() != ID_sva_always)
      expr = sva_always_exprt(expr);

    std::string expr_as_string;
    language->from_expr(expr, expr_as_string, ns);
    messaget message(message_handler);
    message.debug() << "Property: " << expr_as_string << messaget::eom;
    message.debug() << "Mode: " << transition_system.main_symbol->mode
                    << messaget::eom;

    ebmc_propertiest properties;
    properties.properties.push_back(propertyt());
    auto &p = properties.properties.back();
    p.original_expr = expr;
    p.normalized_expr = normalize_property(expr);
    p.mode = transition_system.main_symbol->mode;
    p.location.make_nil();
    p.description = expr_as_string;
    p.name = "command-line assertion";

    return properties;
  }
  else
  {
    // Pull properties from the transition system.
    auto properties =
      from_transition_system(transition_system, message_handler);

    // We optionally may select a subset.
    properties.select_property(cmdline, message_handler);

    return properties;
  }
}
