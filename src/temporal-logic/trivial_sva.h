/*******************************************************************\

Module: Trivial SVA

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TEMPORAL_LOGIC_TRIVIAL_SVA_H
#define CPROVER_TEMPORAL_LOGIC_TRIVIAL_SVA_H

#include <util/expr.h>

/// This applies the following rewrites, removing SVA operators
/// that trivial in the sense that they are state predicates only.
///
/// a sva_iff b --> a <-> b
/// a sva_implies b --> a -> b
/// sva_not a --> ¬a
/// a sva_and b --> a ∧ b                     if a and b are not sequences
/// a sva_or b --> a ∨ b                      if a and b are not sequences
/// sva_overlapped_implication --> a -> b     if a and b are not sequences
/// sva_if --> ? :
/// sva_case --> ? :
/// a sva_disable_iff b --> a ∨ b
/// a sva_accept_on b --> a ∨ b
/// a sva_reject_on b --> ¬a ∧ b
/// a sva_sync_accept_on b --> a ∨ b
/// a sva_sync_reject_on b --> ¬a ∧ b
exprt trivial_sva(exprt);

#endif
