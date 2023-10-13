/*******************************************************************\

Module: Transition Systems for EBMC

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_TRANSITION_SYSTEM_H
#define CPROVER_EBMC_TRANSITION_SYSTEM_H

#include <util/mathematical_expr.h>
#include <util/symbol_table.h>

class cmdlinet;

class transition_systemt
{
public:
  symbol_tablet symbol_table;
  const symbolt *main_symbol;
  optionalt<transt> trans_expr; // transition system expression
};

int get_transition_system(cmdlinet &, transition_systemt &);

#endif // CPROVER_EBMC_TRANSITION_SYSTEM_H
