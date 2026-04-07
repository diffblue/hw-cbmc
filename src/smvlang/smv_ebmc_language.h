/*******************************************************************\

Module: SMV Language Interface

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// SMV Language Interface

#ifndef EBMC_SMV_LANGUAGE_H
#define EBMC_SMV_LANGUAGE_H

#include <ebmc/ebmc_language.h>

class smv_parse_treet;

class smv_ebmc_languaget : public ebmc_languaget
{
public:
  smv_ebmc_languaget(
    const cmdlinet &_cmdline,
    message_handlert &_message_handler)
    : ebmc_languaget(_cmdline, _message_handler)
  {
  }

  // produce the transition system, and return it
  std::optional<transition_systemt> transition_system() override;

protected:
  smv_parse_treet parse();
};

#endif // EBMC_SMV_LANGUAGE_H
