/*******************************************************************\

Module: Verilog Language Interface

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// SMV Language Interface

#ifndef EBMC_VERILOG_LANGUAGE_H
#define EBMC_VERILOG_LANGUAGE_H

#include <ebmc/ebmc_language.h>

#include <filesystem>
#include <iosfwd>

class verilog_parse_treet;
class ebmc_language_filest;

class verilog_ebmc_languaget : public ebmc_languaget
{
public:
  verilog_ebmc_languaget(
    const cmdlinet &_cmdline,
    message_handlert &_message_handler)
    : ebmc_languaget(_cmdline, _message_handler)
  {
  }

  // produce the transition system, and return it
  std::optional<transition_systemt> transition_system() override;

protected:
  void preprocess(const std::filesystem::path &, std::ostream &);
  void preprocess();
  verilog_parse_treet parse(const std::filesystem::path &);
  void show_parse(const std::filesystem::path &);
  void show_parse();
  void parse(const std::filesystem::path &, ebmc_language_filest &);
  void parse(ebmc_language_filest &);
};

#endif // EBMC_VERILOG_LANGUAGE_H
