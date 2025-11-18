/*******************************************************************\

Module: Abstract interface to support a modeling language

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Abstract interface to support a modeling language

#ifndef EBMC_LANGUAGE_H
#define EBMC_LANGUAGE_H

#include <iosfwd>

class cmdlinet;
class message_handlert;
class transition_systemt;

class ebmc_languaget
{
public:
  // constructor / destructor
  ebmc_languaget(cmdlinet &_cmdline, message_handlert &_message_handler)
    : cmdline(_cmdline), message_handler(_message_handler)
  {
  }

  virtual ~ebmc_languaget();

  /// produce diagnostic output as specified on the command line
  virtual void diagnostics() = 0;

  /// produce the transition system, and return it
  virtual transition_systemt transition_system() = 0;

protected:
  cmdlinet &cmdline;
  message_handlert &message_handler;
};

#endif // EBMC_LANGUAGE_H
