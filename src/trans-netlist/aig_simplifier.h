/*******************************************************************\

Module: AIG Simplifier

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// AIG Simplifier using Equivalences

#ifndef CPROVER_TRANS_NETLIST_AIG_SIMPLIFIER_H
#define CPROVER_TRANS_NETLIST_AIG_SIMPLIFIER_H

#include "aig.h"

#include <utility>
#include <vector>

using substitutiont = std::vector<literalt>;

/// Applies a substitution map to a literal.
/// \param l: The literal to substitute
/// \param substitution: Map from variable numbers to replacement literals
/// \return The substituted literal
literalt apply_substitution(literalt l, const substitutiont &);

/// A pair of equivalent literals
using equivalencet = std::pair<literalt, literalt>;

/// A vector of equivalences between literals
using equivalencest = std::vector<equivalencet>;

/// Simplifies an AIG by substituting equivalent nodes.
/// Given a set of equivalences, this function creates a new AIG
/// where equivalent nodes are merged. For each equivalence (l1, l2),
/// references to the node with the larger variable number are
/// replaced with references to the node with the smaller variable number.
/// Constant propagation is performed when an equivalence makes a node constant.
/// \param src: The source AIG to simplify
/// \param equivalences: Vector of pairs of equivalent literals
/// \return The simplified AIG
std::pair<aigt, substitutiont>
aig_simplify(const aigt &, const equivalencest &);

#endif // CPROVER_TRANS_NETLIST_AIG_SIMPLIFIER_H
