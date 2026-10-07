/*******************************************************************\

Module: Cone of Influence Reduction

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TRANS_WORD_LEVEL_CONE_OF_INFLUENCE_H
#define CPROVER_TRANS_WORD_LEVEL_CONE_OF_INFLUENCE_H

#include <util/mathematical_expr.h>
#include <util/message.h>

/// The result of a cone-of-influence reduction
struct cone_of_influence_resultt
{
  /// The reduced transition system
  transt trans;

  /// Statistics, for reporting
  struct statisticst
  {
    std::size_t invar_constraints = 0, invar_constraints_kept = 0;
    std::size_t init_constraints = 0, init_constraints_kept = 0;
    std::size_t trans_constraints = 0, trans_constraints_kept = 0;
    std::size_t state_variables = 0, state_variables_kept = 0;
    /// The number of definitions that were treated as general
    /// constraints owing to a definitional cycle
    std::size_t cyclic_definitions = 0;

    std::size_t constraints() const
    {
      return invar_constraints + init_constraints + trans_constraints;
    }

    std::size_t constraints_kept() const
    {
      return invar_constraints_kept + init_constraints_kept +
             trans_constraints_kept;
    }
  } statistics;

  void report(messaget &) const;
};

/// Reduce the given transition system to the cone of influence of the
/// symbols in \p seeds.
///
/// The conjuncts of the transition system's invariant, initial-state and
/// transition constraints are classified into _definitions_ and _general
/// constraints_. A definition has the shape `v == e` (in the invariant or
/// initial-state constraint) or `next(v) == e` (in the transition
/// constraint), where `v` is a symbol. All other conjuncts are general
/// constraints.
///
/// All general constraints are kept. The definitions that are kept are
/// those of the variables that the seeds or the general constraints depend
/// on, transitively. All other definitions are removed.
///
/// Soundness. Removing conjuncts yields an over-approximation: every trace
/// of the original system is a trace of the reduced one. Hence, PROVED
/// verdicts obtained on the reduced system (from BMC or k-induction) are
/// sound without further assumptions. The converse direction, i.e., that a
/// trace of the reduced system extends to a trace of the original one, is
/// what makes REFUTED verdicts and witnesses for existential properties
/// sound. The argument is as follows: the removed conjuncts are all
/// definitions of variables that are not in the cone, and these variables
/// do not occur in any kept conjunct. Given a trace of the reduced system,
/// the removed variables can be assigned by evaluating their definitions
/// in dependency order, timeframe by timeframe, provided that
///
/// 1. each removed variable has at most one definition per timeframe,
/// 2. the removed definitions are acyclic within a timeframe, and
/// 3. the right-hand side of each removed definition evaluates to a value
///    in the domain of the variable.
///
/// Definitions that violate 1 (e.g., two invariant definitions of the
/// same variable, or an invariant definition together with an
/// initial-state or next-state definition) or 2 (e.g., `a == !b` and
/// `b == a`; cycles may also go through next-state symbols, e.g.,
/// `next(a) == next(b)` and `b == !a`) are treated as general
/// constraints. For 3, only variables whose type covers the full set of
/// bit patterns (Booleans, bit-vectors, and arrays and structs thereof)
/// are considered to have definitions; the backends encode SMV range and
/// enumeration types as bit-vectors, may constrain the variable to its
/// domain, and implement a narrowing cast as a truncation, which may thus
/// yield a value outside the domain.
///
/// Assumptions must be passed as seeds, as the reduced system is
/// combined with them. Note that the argument above relies on all
/// constraints on the removed variables being definitions; this must be
/// revisited if assumptions are ever dropped as well.
cone_of_influence_resultt
cone_of_influence(const transt &, const exprt::operandst &seeds);

#endif // CPROVER_TRANS_WORD_LEVEL_CONE_OF_INFLUENCE_H
