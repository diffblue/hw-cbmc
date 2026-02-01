/*******************************************************************\

Module: AIG Reorder

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// AIG Reorder

#ifndef CPROVER_TRANS_NETLIST_AIG_REORDER_H
#define CPROVER_TRANS_NETLIST_AIG_REORDER_H

#include "aig.h"
#include "aig_substitution.h"

#include <utility>

/// Rebuild an AIG in dependency order, applying a substitution.
/// The substitution maps old variable numbers to replacement literals.
/// Nodes where subst[i] == literalt(i, false) are kept; all others
/// are replaced. The resulting AIG is in topological order.
std::pair<aigt, aig_substitution_mapt>
aig_reorder(const aigt &, const aig_substitution_mapt &substitution);

#endif // CPROVER_TRANS_NETLIST_AIG_REORDER_H
