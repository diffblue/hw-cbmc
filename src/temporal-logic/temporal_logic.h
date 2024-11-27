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

/// Returns true iff the given expression has a CTL operator
/// as its root
bool is_CTL_operator(const exprt &);

/// Returns true iff the given expression contains a CTL operator
bool has_CTL_operator(const exprt &);

/// Returns true iff the given expression is an LTL formula
bool is_LTL(const exprt &);

/// Returns true iff the given expression is of the form Gp
bool is_Gp(const exprt &);

/// Returns true iff the given expression has an LTL operator
/// as its root
bool is_LTL_operator(const exprt &);

/// Returns true iff the given expression is an SVA sequence expression
bool is_SVA_sequence(const exprt &);

/// Returns true iff the given expression is an SVA temporal operator
bool is_SVA_operator(const exprt &);

/// Returns true iff the given expression is an SVA expression
bool is_SVA(const exprt &);

/// Returns true iff the given expression is an SVA expression that
/// we can convert into a Buechi automaton
bool is_Buechi_SVA(const exprt &);

#endif
