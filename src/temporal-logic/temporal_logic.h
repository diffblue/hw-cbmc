/*******************************************************************\

Module: Temporal Logic

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TEMPORAL_LOGIC_H
#define CPROVER_TEMPORAL_LOGIC_H

#include <util/expr.h>

/// Returns true iff the given expression contains a temporal operator
bool has_temporal_operator(const exprt &);

#endif
