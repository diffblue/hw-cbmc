/*******************************************************************\

Module: AIG Nondet Elimination

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// AIG Nondet Elimination

#ifndef CPROVER_TRANS_NETLIST_AIG_NONDET_ELIMINATION_H
#define CPROVER_TRANS_NETLIST_AIG_NONDET_ELIMINATION_H

#include "aig.h"
#include "aig_substitution.h"

#include <utility>

/// Eliminate nondet (input) nodes from an AIG using equivalences.
/// For each equivalence between a nondet node and another node,
/// the nondet is replaced by the other node. The resulting AIG
/// is re-sorted in dependency order.
/// Returns the new AIG and a substitution map (old var_no -> new literal).
std::pair<aigt, aig_substitution_mapt> aig_nondet_elimination(
  const aigt &,
  const aig_plus_constraintst::equivalencest &);

#endif // CPROVER_TRANS_NETLIST_AIG_NONDET_ELIMINATION_H
