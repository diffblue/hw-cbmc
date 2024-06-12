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
/// sva_overlapped_implication --> ¬a ∨ b
/// sva_non_overlapped_implication --> ¬a ∨ Xb
/// sva_nexttime φ --> Xφ
/// sva_s_nexttime φ --> Xφ
/// sva_if --> ? :
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
