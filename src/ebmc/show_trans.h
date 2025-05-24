/*******************************************************************\

Module: Show Transition Relation in various Formats

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_EBMC_SHOW_TRANS_H
#define CPROVER_EBMC_SHOW_TRANS_H

#include "transition_system.h"

int show_trans_verilog_rtl(const transition_systemt &, std::ostream &);
int show_trans_verilog_netlist(const transition_systemt &, std::ostream &);
int show_trans_smv_netlist(const transition_systemt &, std::ostream &);
int show_trans(const transition_systemt &, std::ostream &);

#endif // CPROVER_EBMC_SHOW_TRANS_H
