/*******************************************************************\

Module: Property Normalization

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TEMPORAL_LOGIC_NORMALIZE_PROPERTY_H
#define CPROVER_TEMPORAL_LOGIC_NORMALIZE_PROPERTY_H

#include <util/expr.h>

/// This applies the following rewrites:
/// cover(φ) --> G¬φ
/// ¬(a ∨ b) --> ¬a ∧ ¬b
/// ¬(a ∧ b) --> ¬a ∨ ¬b
/// (a -> b) --> ¬a ∨ b
/// a sva_iff b --> a <-> b
/// a sva_implies b --> a -> b
/// sva_not a --> ¬a
/// a sva_and b --> a ∧ b                       if a and b are not SVA sequences
/// a sva_or b --> a ∨ b                        if a and b are not SVA sequences
/// sva_overlapped_implication --> ¬a ∨ b       if a and b are not SVA sequences
/// sva_non_overlapped_implication --> ¬a ∨ Xb  if a and b are not SVA sequences
/// sva_nexttime φ --> Xφ
/// sva_nexttime[i] φ --> sva_always[i:i] φ
/// sva_s_nexttime φ --> Xφ
/// sva_s_nexttime[i] φ --> sva_s_always[i:i] φ
/// sva_if --> ? :
/// a sva_disable_iff b --> a ∨ b
/// a sva_accept_on b --> a ∨ b
/// a sva_reject_on b --> ¬a ∧ b
/// a sva_sync_accept_on b --> a ∨ b
/// a sva_sync_reject_on b --> ¬a ∧ b
/// ¬Xφ --> X¬φ
/// ¬¬φ --> φ
/// ¬Gφ --> F¬φ
/// ¬Fφ --> G¬φ
/// [*] φ --> F φ
/// [+] φ --> X F φ
/// strong(φ) --> φ
/// weak(φ) --> φ
/// sva_case --> ? :
exprt normalize_property(exprt);

#endif
