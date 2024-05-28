/*******************************************************************\

Module: Transition Systems for EBMC

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_TRANSITION_SYSTEM_H
#define CPROVER_EBMC_TRANSITION_SYSTEM_H

#include <util/mathematical_expr.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

class cmdlinet;
class message_handlert;

class transition_systemt
{
public:
  transition_systemt()
    : trans_expr{ID_trans, true_exprt(), true_exprt(), true_exprt(), typet()}
  {
  }

  symbol_tablet symbol_table;
  const symbolt *main_symbol;
  transt trans_expr; // transition system expression

  void output(std::ostream &) const;

  std::vector<symbol_exprt> state_variables() const;
  std::vector<symbol_exprt> inputs() const;
};

transition_systemt get_transition_system(const cmdlinet &, message_handlert &);

int preprocess(const cmdlinet &, message_handlert &);
int show_parse(const cmdlinet &, message_handlert &);
int show_modules(const cmdlinet &, message_handlert &);
int show_module_hierarchy(const cmdlinet &, message_handlert &);
int show_symbol_table(const cmdlinet &, message_handlert &);

#endif // CPROVER_EBMC_TRANSITION_SYSTEM_H
