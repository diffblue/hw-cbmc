/*******************************************************************\

Module: SVA Monitor

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_TEMPORAL_LOGIC_SVA_MONITOR_H
#define CPROVER_TEMPORAL_LOGIC_SVA_MONITOR_H

class transition_systemt;
class ebmc_propertiest;

void sva_monitor(transition_systemt &, ebmc_propertiest &);

#endif
