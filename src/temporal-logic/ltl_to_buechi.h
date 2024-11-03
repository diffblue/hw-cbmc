/*******************************************************************\

Module: Property Instrumentation via Buechi Automata

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_LTL_TO_BUECHI_H
#define CPROVER_EBMC_LTL_TO_BUECHI_H

#include <util/expr.h>

struct buechi_transt
{
  exprt init;
  exprt trans;
  exprt liveness_signal;
};

class message_handlert;

buechi_transt ltl_to_buechi(
  const exprt &formula,
  const std::string &identifier_prefix,
  message_handlert &);

#endif
