/*******************************************************************\

Module: Transition Systems for EBMC

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_EBMC_BUILD_TRANSITION_SYSTEM_H
#define CPROVER_EBMC_BUILD_TRANSITION_SYSTEM_H

class cmdlinet;
class message_handlert;
class transition_systemt;

transition_systemt get_transition_system(const cmdlinet &, message_handlert &);

int preprocess(const cmdlinet &, message_handlert &);
int show_parse(const cmdlinet &, message_handlert &);
int show_modules(const cmdlinet &, message_handlert &);
int show_module_hierarchy(const cmdlinet &, message_handlert &);
int show_symbol_table(const cmdlinet &, message_handlert &);

#endif // CPROVER_EBMC_BUILD_TRANSITION_SYSTEM_H
