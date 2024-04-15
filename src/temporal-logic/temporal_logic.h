/*******************************************************************\

Module: Temporal Logic

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TEMPORAL_LOGIC_H
#define CPROVER_TEMPORAL_LOGIC_H

#include <util/expr.h>

/// Returns true iff the given expression contains a temporal operator
bool has_temporal_operator(const exprt &);

/// Returns true iff the given expression has a temporal operator
/// as its root
bool is_temporal_operator(const exprt &);

/// Returns true iff the given expression is an existential path
/// property.
bool is_exists_path(const exprt &);

#endif
