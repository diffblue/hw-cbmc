/*******************************************************************\

Module: Unwinding the Properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_PROPERTY_H
#define CPROVER_TRANS_PROPERTY_H

#include <util/symbol_table.h>
#include <util/message.h>
#include <util/namespace.h>

#include <solvers/prop/prop.h>
#include <solvers/prop/prop_conv.h>

#include "bmc_map.h"

// bit-level
void property(
  const std::list<exprt> &properties,
  std::list<bvt> &prop_bv,
  message_handlert &,
  propt &solver,
  const bmc_mapt &map,
  const namespacet &);

// word-level
void property(
  const std::list<exprt> &properties,
  std::list<bvt> &prop_bv,
  message_handlert &,
  prop_convt &solver,
  unsigned no_timeframes,
  const namespacet &);

#endif
