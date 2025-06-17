/*******************************************************************\

Module: SVA to LTL

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TEMPORAL_LOGIC_SVA_TO_LTL_H
#define CPROVER_TEMPORAL_LOGIC_SVA_TO_LTL_H

#include <util/expr.h>

/// If possible, this maps an SVA expression to an equivalent LTL
/// expression, or otherwise returns {}.
std::optional<exprt> SVA_to_LTL(exprt);

#endif
