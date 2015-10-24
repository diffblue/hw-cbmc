/*******************************************************************\

Module: Extracting Counterexamples

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BMC_COUNTEREXAMPLE_H
#define CPROVER_BMC_COUNTEREXAMPLE_H

#include <util/namespace.h>
#include <util/message.h>

#include <solvers/prop/prop.h>
#include <langapi/language_ui.h>

#include "bmc_map.h"

// netlist

void show_counterexample(
  const std::list<exprt> &properties,
  const std::list<bvt> &prop_bv,
  message_handlert &,
  const propt &solver,
  const bmc_mapt &map,
  const namespacet &ns,
  language_uit::uit ui);

void show_counterexample(
  message_handlert &,
  const propt &solver,
  const bmc_mapt &map,
  const namespacet &ns,
  language_uit::uit ui);

#endif
