/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_UNWIND_H
#define CPROVER_TRANS_UNWIND_H

#include <util/mathematical_expr.h>
#include <util/message.h>
#include <util/std_expr.h>

// word-level

void unwind(const transt &trans, message_handlert &message_handler,
            class decision_proceduret &decision_procedure,
            unsigned no_timeframes, const class namespacet &ns,
            bool initial_state = true);

#endif
