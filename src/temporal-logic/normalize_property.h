/*******************************************************************\

Module: Property Normalization

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TEMPORAL_LOGIC_NORMALIZE_PROPERTY_H
#define CPROVER_TEMPORAL_LOGIC_NORMALIZE_PROPERTY_H

#include <util/expr.h>

/// This applies the following rewrites:
///
/// cover(φ) --> G¬φ
///
/// -----Propositional-----
/// ¬(a ∨ b) --> ¬a ∧ ¬b
/// ¬(a ∧ b) --> ¬a ∨ ¬b
/// (a -> b) --> ¬a ∨ b
///
/// -----SVA-----
/// a sva_iff b --> a <-> b
/// a sva_implies b --> a -> b
/// sva_not a --> ¬a
/// a sva_and b --> a ∧ b                                   if a and b are not SVA sequences
/// a sva_or b --> a ∨ b                                    if a and b are not SVA sequences
/// sva_overlapped_implication --> ¬a ∨ b                   if a is not an SVA sequence
/// sva_non_overlapped_implication --> ¬a ∨ sva_nexttime b  if a is not an SVA sequence
/// sva_nexttime φ --> Xφ
/// sva_nexttime[i] φ --> sva_always[i:i] φ
/// sva_s_nexttime φ --> Xφ
/// sva_s_nexttime[i] φ --> sva_s_always[i:i] φ
/// sva_if --> ? :
/// ##[0:$] φ --> s_eventually φ
/// ##[i:$] φ --> s_nexttime[i] s_eventually φ
/// ##[*] φ --> F φ
/// ##[+] φ --> X F φ
/// strong(φ) --> φ
/// weak(φ) --> φ
/// sva_case --> ? :
/// a sva_disable_iff b --> a ∨ b
/// a sva_accept_on b --> a ∨ b
/// a sva_reject_on b --> ¬a ∧ b
/// a sva_sync_accept_on b --> a ∨ b
/// a sva_sync_reject_on b --> ¬a ∧ b
/// ¬ sva_s_eventually φ --> sva_always ¬φ
/// ¬ sva_always φ --> sva_s_eventually ¬φ
///
/// ----LTL-----
/// ¬Xφ --> X¬φ
/// ¬¬φ --> φ
/// ¬Gφ --> F¬φ
/// ¬Fφ --> G¬φ
exprt normalize_property(exprt);

#endif
