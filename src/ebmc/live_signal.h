/*******************************************************************\

Module: Liveness Signal

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef EBMC_LIVE_SIGNAL_H
#define EBMC_LIVE_SIGNAL_H

#include <util/expr.h>

class transition_systemt;

void set_liveness_signal(transition_systemt &, exprt property);

#endif // EBMC_LIVE_SIGNAL_H
