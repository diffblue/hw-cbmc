/*******************************************************************\

Module: Buechi Automaton Instrumentation

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "instrument_buechi.h"

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
    if(
      !is_LTL(property.normalized_expr) &&
      !is_Buechi_SVA(property.normalized_expr))
    {
      continue;
    }

    messaget message(message_handler);
    message.debug() << "Translating " << property.description << " to Buechi"
                    << messaget::eom;

    // make the automaton for the negation of the property
    auto buechi = ltl_to_buechi(
      not_exprt{property.normalized_expr}, "buechi::", message_handler);

    // add the automaton to the transition system
    transition_system.trans_expr.init() =
      and_exprt{transition_system.trans_expr.init(), buechi.init};

    transition_system.trans_expr.trans() =
      and_exprt{transition_system.trans_expr.trans(), buechi.trans};

    // replace the normalized property expression
    property.normalized_expr = G_exprt{F_exprt{buechi.liveness_signal}};
  }
}
