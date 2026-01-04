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

protected:
  void preprocess(const std::filesystem::path &, std::ostream &);
  void preprocess();
  verilog_parse_treet parse(const std::filesystem::path &);
  void show_parse(const std::filesystem::path &);
  void show_parse();

  parse_treest parse();

  // base_name of the top-level module
  irep_idt top_level_module(const parse_treest &) const;

  class modulet
  {
  public:
    irep_idt identifier;
    bool type_checked = false, in_progress = false;
    const parse_treet &parse_tree;
    modulet(irep_idt _identifier, const parse_treet &_parse_tree)
      : identifier(_identifier), parse_tree(_parse_tree)
    {
    }
  };

  std::map<irep_idt, modulet> module_map;

  transition_systemt typecheck(const parse_treest &);
  void typecheck_module(modulet &, symbol_tablet &);
};

#endif // EBMC_VERILOG_LANGUAGE_H
