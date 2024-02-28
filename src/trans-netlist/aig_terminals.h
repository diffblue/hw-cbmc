/*******************************************************************\

Module: AND-Inverter Graph Terminals

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// AND-Inverter Graph Terminals

#ifndef CPROVER_TRANS_NETLIST_AIG_TERMINALS_H
#define CPROVER_TRANS_NETLIST_AIG_TERMINALS_H

#include "aig.h"

typedef std::set<literalt::var_not> aig_terminal_sett;
typedef std::map<literalt::var_not, aig_terminal_sett> aig_terminalst;

// produces the support set of the given AIG
aig_terminalst terminals(const aigt &);

#endif // CPROVER_TRANS_NETLIST_AIG_TERMINALS_H
