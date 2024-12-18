/*******************************************************************\

Module: Netlists for EBMC

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_NETLIST_H
#define CPROVER_EBMC_NETLIST_H

#include "ebmc_properties.h"
#include "transition_system.h"

class netlistt;

netlistt
make_netlist(transition_systemt &, ebmc_propertiest &, message_handlert &);

#endif // CPROVER_EBMC_NETLIST_H
