/*******************************************************************\

Module: AIGER Language Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// AIGER Language Interface

#ifndef CPROVER_AIGER_EBMC_LANGUAGE_H
#define CPROVER_AIGER_EBMC_LANGUAGE_H

#include <ebmc/ebmc_language.h>

class aiger_ebmc_languaget : public ebmc_languaget
{
public:
  aiger_ebmc_languaget(
    const cmdlinet &_cmdline,
    message_handlert &_message_handler)
    : ebmc_languaget(_cmdline, _message_handler)
  {
  }

  std::optional<transition_systemt> transition_system() override;
};

#endif // CPROVER_AIGER_EBMC_LANGUAGE_H
