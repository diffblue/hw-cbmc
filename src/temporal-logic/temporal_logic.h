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

/// Returns true iff the given expression is a CTL formula
bool is_CTL(const exprt &);

/// Returns true iff the given expression is AGp
bool is_AGp(const exprt &);

/// Returns true iff the given expression has a CTL operator
/// as its root
bool is_CTL_operator(const exprt &);

/// Returns true iff the given expression contains a CTL operator
bool has_CTL_operator(const exprt &);

/// Returns true iff the given expression has a real-time CTL operator
/// as its root
bool is_RTCTL_operator(const exprt &);

/// Returns true iff the given expression contains a real-time CTL operator
bool has_RTCTL_operator(const exprt &);

/// Returns true iff the given expression is an LTL formula
bool is_LTL(const exprt &);

/// Returns true iff the given expression is Gp
bool is_Gp(const exprt &);

/// Returns true iff the given expression is GFp
bool is_GFp(const exprt &);

/// Returns true iff the given expression is an LTL past formula
bool is_LTL_past(const exprt &);

/// Returns true iff the given expression has an LTL operator
/// as its root
bool is_LTL_operator(const exprt &);

/// Returns true iff the given expression has an LTL past operator
/// as its root
bool is_LTL_past_operator(const exprt &);

/// Returns true iff the given expression is an SVA sequence expression
bool is_SVA_sequence_operator(const exprt &);

/// Returns true iff the given expression is an SVA temporal operator
bool is_SVA_operator(const exprt &);

/// Returns true iff the given expression is an SVA expression
bool is_SVA(const exprt &);

/// Returns true iff the given expression is always p
bool is_SVA_always_p(const exprt &);

/// Returns true iff the given expression is always s_eventually p
bool is_SVA_always_s_eventually_p(const exprt &);

/// Turns some fragment of LTL into equivalent CTL, or
/// returns {} if not possible
std::optional<exprt> LTL_to_CTL(exprt);

/// If possible, this maps an SVA expression to an equivalent LTL
/// expression, or otherwise returns {}.
std::optional<exprt> SVA_to_LTL(exprt);

#endif
