/*******************************************************************\

Module: Show Transition Relation in various Formats

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_EBMC_SHOW_TRANS_H
#define CPROVER_EBMC_SHOW_TRANS_H

#include <util/cmdline.h>
#include <util/ui_message.h>

int show_trans_verilog_rtl(const cmdlinet &, ui_message_handlert &);
int show_trans_verilog_netlist(const cmdlinet &, ui_message_handlert &);
int show_trans_smv_netlist(const cmdlinet &, ui_message_handlert &);
int show_trans(const cmdlinet &, ui_message_handlert &);

#endif
