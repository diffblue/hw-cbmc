/*******************************************************************\

Module: VHDL Language Interface

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// VHDL Language Interface

#ifndef CPROVER_VHDL_VHDL_EBMC_LANGUAGE_H
#define CPROVER_VHDL_VHDL_EBMC_LANGUAGE_H

#include <util/irep.h>

#include <ebmc/ebmc_language.h>

#include <filesystem>

class vhdl_parse_treet;

class vhdl_ebmc_languaget : public ebmc_languaget
{
public:
  vhdl_ebmc_languaget(
    const cmdlinet &_cmdline,
    message_handlert &_message_handler)
    : ebmc_languaget(_cmdline, _message_handler)
  {
  }

  // produce the transition system, and return it
  std::optional<transition_systemt> transition_system() override;

protected:
  /// parse all files given on the command line into one parse tree
  vhdl_parse_treet parse();

  /// parse one file, appending to the given parse tree
  void parse(const std::filesystem::path &, vhdl_parse_treet &);

  /// the entity selected with --top, or the only entity
  irep_idt top_level_entity(const vhdl_parse_treet &);
};

#endif // CPROVER_VHDL_VHDL_EBMC_LANGUAGE_H
