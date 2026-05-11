/*******************************************************************\

Module: Property Normalization

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TEMPORAL_LOGIC_NORMALIZE_PROPERTY_H
#define CPROVER_TEMPORAL_LOGIC_NORMALIZE_PROPERTY_H

#include <util/expr.h>

/// This applies the following rewrites, in addition to the ones
/// done by \ref trivial_sva:
///
/// -----SVA-----
/// sva_nexttime φ --> sva_always[1:1] φ
/// sva_nexttime[i] φ --> sva_always[i:i] φ
/// sva_s_nexttime φ --> sva_always[1:1] φ
/// sva_s_nexttime[i] φ --> sva_s_always[i:i] φ
/// cover φ --> sva_always_exprt ¬φ
/// a sva_disable_iff b --> a ∨ b  unless used in cover φ
/// a sva_disable_iff b --> ¬a ∧ b  when used in cover φ
///
exprt normalize_property(exprt);

#endif
