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
/// sva_non_overlapped_implication --> ¬a ∨ always[1:1] b   if a is not an SVA sequence
/// sva_nexttime φ --> sva_always[1:1] φ
/// sva_nexttime[i] φ --> sva_always[i:i] φ
/// sva_s_nexttime φ --> sva_always[1:1] φ
/// sva_s_nexttime[i] φ --> sva_s_always[i:i] φ
/// ##[0:$] φ --> s_eventually φ
/// ##[i:$] φ --> s_nexttime[i] s_eventually φ
/// ##[*] φ --> s_eventually φ
/// ##[+] φ --> always[1:1] s_eventually φ
/// strong(φ) --> φ
/// weak(φ) --> φ
/// ¬ sva_s_eventually φ --> sva_always ¬φ
/// ¬ sva_always φ --> sva_s_eventually ¬φ
/// cover φ --> sva_always_exprt ¬φ
///
/// ----LTL-----
/// ¬Xφ --> X¬φ
/// ¬¬φ --> φ
/// ¬Gφ --> F¬φ
/// ¬Fφ --> G¬φ
/// false R ψ --> G ψ
exprt normalize_property(exprt);

#endif
