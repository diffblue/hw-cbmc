/*******************************************************************\

Module: Buechi Automaton Instrumentation

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "instrument_buechi.h"

#include <util/format_expr.h>

#include <temporal-logic/ltl.h>
#include <temporal-logic/ltl_to_buechi.h>
#include <temporal-logic/temporal_logic.h>

void instrument_buechi(
  transition_systemt &transition_system,
  ebmc_propertiest &properties,
  message_handlert &message_handler)
{
  for(auto &property : properties.properties)
  {
    if(!property.is_unknown())
      continue;

    // This is for LTL and some fragment of SVA only.
    if(!is_LTL(property.normalized_expr) && !is_SVA(property.normalized_expr))
    {
      property.unsupported("not convertible to Buechi");
      continue;
    }

    messaget message(message_handler);
    message.debug() << "Translating " << property.description << " to Buechi"
                    << messaget::eom;

    try
    {
      // make the automaton for the negation of the property
      auto buechi =
        ltl_to_buechi(not_exprt{property.normalized_expr}, message_handler);

      // make a fresh symbol for the state of the automaton
      namespacet ns(transition_system.symbol_table);
      auto property_symbol = ns.lookup(property.identifier);

      auxiliary_symbolt new_state_symbol{
        id2string(property_symbol.name) + "::buechi_state",
        buechi.state_symbol.type(),
        property_symbol.mode};
      new_state_symbol.is_state_var = true;
      new_state_symbol.module = property_symbol.module;

      buechi.rename_state_symbol(new_state_symbol.symbol_expr());

      // add the new symbol to the symbol table
      transition_system.symbol_table.add(std::move(new_state_symbol));

      // add the automaton to the transition system
      transition_system.trans_expr.init() =
        and_exprt{transition_system.trans_expr.init(), buechi.init};

      transition_system.trans_expr.trans() =
        and_exprt{transition_system.trans_expr.trans(), buechi.trans};

      // Replace the normalized property expression
      // by the Buechi acceptance condition.
      exprt::operandst property_conjuncts;

      bool have_liveness = false, have_safety = false;

      if(!buechi.liveness_signal.is_false())
      {
        // Note that we have negated the property,
        // so this is the negation of the Buechi acceptance condition.
        property_conjuncts.push_back(
          F_exprt{G_exprt{not_exprt{buechi.liveness_signal}}});
        have_liveness = true;
      }

      if(!buechi.error_signal.is_true())
      {
        property_conjuncts.push_back(G_exprt{not_exprt{buechi.error_signal}});
        have_safety = true;
      }

      if(have_liveness && have_safety)
        message.debug() << "Buechi automaton has liveness and safety components"
                        << messaget::eom;
      else if(have_liveness)
        message.debug() << "Buechi automaton is liveness only" << messaget::eom;
      else if(have_safety)
        message.debug() << "Buechi automaton is safety only" << messaget::eom;

      property.normalized_expr = conjunction(property_conjuncts);

      message.debug() << "New property: " << format(property.normalized_expr)
                      << messaget::eom;
    }
    catch(ltl_to_buechi_unsupportedt error)
    {
      property.unsupported(
        error.expr.id_string() + " not convertible to Buechi");
      continue;
    }
  }
}
