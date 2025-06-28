/*******************************************************************\

Module: Rewrite SVA Sequences

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TEMPORAL_LOGICS_REWRITE_SVA_SEQUENCE_H
#define CPROVER_TEMPORAL_LOGICS_REWRITE_SVA_SEQUENCE_H

#include <util/expr.h>

/// 1800-2017 F.4.3
/// Returns true iff the given SVA sequence admits an empty match.
bool admits_empty(const exprt &);

/// Implements the rewriting rules in 1800-2017 16.9.2.1.
/// The resulting sequence expression do not admit empty matches.
exprt rewrite_sva_sequence(exprt);

#endif // CPROVER_TEMPORAL_LOGICS_REWRITE_SVA_SEQUENCE_H
