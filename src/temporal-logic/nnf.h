/*******************************************************************\

Module: Negation Normal Form for temporal logic

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TEMPORAL_LOGIC_NNF_H
#define CPROVER_TEMPORAL_LOGIC_NNF_H

#include <util/expr.h>

/// Negates a single node (i.e., not recursively) of a temporal logic formula.
/// Returns {} if no negation is known.
std::optional<exprt> negate_property_node(const exprt &);

#endif
