/*******************************************************************\

Module: Verilog Language Interface

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// SMV Language Interface

#ifndef EBMC_VERILOG_LANGUAGE_H
#define EBMC_VERILOG_LANGUAGE_H

#include <ebmc/ebmc_language.h>

#include "verilog_parse_tree.h"

#include <filesystem>
#include <iosfwd>
#include <map>

class symbol_tablet;
class verilog_scopest;

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

  /// a Verilog parse tree forest
  using parse_treet = verilog_parse_treet;
  using parse_treest = std::list<parse_treet>;

  void preprocess(const std::filesystem::path &, std::ostream &);
  void preprocess();
  void show_parse(const std::filesystem::path &);
  void show_parse();

  parse_treest parse();
  symbol_tablet elaborate_compilation_units(const parse_treest &);

protected:
  verilog_parse_treet parse(const std::filesystem::path &, verilog_scopest &);

  void copy_parse_tree(const parse_treet &, symbol_tablet &);

  class modulet
  {
  public:
    irep_idt identifier;
    const parse_treet &parse_tree;
    modulet(irep_idt _identifier, const parse_treet &_parse_tree)
      : identifier(_identifier), parse_tree(_parse_tree)
    {
    }
  };
  transition_systemt typecheck(
    const parse_treest &,
    const std::vector<irep_idt> &top_level_modules,
    symbol_tablet &&);
  void typecheck_module(modulet &, symbol_tablet &);

  void create_root_module(
    const std::vector<irep_idt> &top_level_modules,
    verilog_standardt,
    transition_systemt &);

  void create_reset_logic(const std::string &, transition_systemt &);
};

#endif // EBMC_VERILOG_LANGUAGE_H
