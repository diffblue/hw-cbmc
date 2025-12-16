/*******************************************************************\

Module: Transition Systems for EBMC

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_BUILD_TRANSITION_SYSTEM_H
#define CPROVER_EBMC_BUILD_TRANSITION_SYSTEM_H

#include "ebmc_language.h"

transition_systemt get_transition_system(const cmdlinet &, message_handlert &);

void preprocess(const cmdlinet &, message_handlert &);
int show_parse(const cmdlinet &, message_handlert &);
int show_modules(const cmdlinet &, message_handlert &);
int show_module_hierarchy(const cmdlinet &, message_handlert &);
int show_symbol_table(const cmdlinet &, message_handlert &);

class ebmc_languagest : public ebmc_languaget
{
public:
  ebmc_languagest(cmdlinet &_cmdline, message_handlert &_message_handler)
    : ebmc_languaget{_cmdline, _message_handler}
  {
  }

  std::optional<transition_systemt> transition_system() override;
};

#endif // CPROVER_EBMC_BUILD_TRANSITION_SYSTEM_H
