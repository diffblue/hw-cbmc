/*******************************************************************\

Module: BTOR2 Language Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// BTOR2 Language Interface

#ifndef CPROVER_BTOR_EBMC_LANGUAGE_H
#define CPROVER_BTOR_EBMC_LANGUAGE_H

#include <ebmc/ebmc_language.h>

class btor_ebmc_languaget : public ebmc_languaget
{
public:
  btor_ebmc_languaget(
    const cmdlinet &_cmdline,
    message_handlert &_message_handler)
    : ebmc_languaget(_cmdline, _message_handler)
  {
  }

  std::optional<transition_systemt> transition_system() override;
};

#endif // CPROVER_BTOR_EBMC_LANGUAGE_H
