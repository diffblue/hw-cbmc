/*******************************************************************\

Module: SMV Netlists

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TRANS_NETLIST_SMV_NETLIST_H
#define CPROVER_TRANS_NETLIST_SMV_NETLIST_H

#include <util/irep.h>

#include "netlist.h"

#include <string>

std::string id2smv(const irep_idt &);

void smv_netlist(const netlistt &, const namespacet &, std::ostream &);

#endif // CPROVER_TRANS_NETLIST_SMV_NETLIST_H
