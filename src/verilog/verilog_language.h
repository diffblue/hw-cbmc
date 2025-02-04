/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_LANGUAGE_H
#define CPROVER_VERILOG_LANGUAGE_H

#include <util/options.h>

#include <langapi/language.h>

#include "verilog_parse_tree.h"
#include "verilog_scope.h"

class verilog_languaget:public languaget
{
public:
  bool preprocess(
    std::istream &,
    const std::string &path,
    std::ostream &,
    message_handlert &) override;

  bool
  parse(std::istream &, const std::string &path, message_handlert &) override;

  void dependencies(
    const std::string &module,
    std::set<std::string> &module_set) override;
                            
  void modules_provided(
    std::set<std::string> &module_set) override;

  bool interfaces(symbol_table_baset &, message_handlert &) override;

  bool typecheck(
    symbol_table_baset &,
    const std::string &module,
    message_handlert &) override;

  void show_parse(std::ostream &, message_handlert &) override;

  ~verilog_languaget() override { }
  
  bool from_expr(
    const exprt &expr, std::string &code,
    const namespacet &ns) override;

  bool from_type(
    const typet &type, std::string &code,
    const namespacet &ns) override;

  bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &,
    const namespacet &,
    message_handlert &) override;

  bool
  generate_support_functions(symbol_table_baset &, message_handlert &) override
  {
    return false;
  }

  std::unique_ptr<languaget> new_language() override
  {
    return std::make_unique<verilog_languaget>();
  }

  std::string id() const override { return "Verilog"; }
  std::string description() const override { return "Verilog"; }

  std::set<std::string> extensions() const override
  { 
    return { "v", "sv" };
  }

  void set_language_options(const optionst &, message_handlert &) override;

  verilog_parse_treet &get_parse_tree()
  {
    return parse_tree;
  }

  verilog_languaget() : parse_tree(verilog_standardt::NOT_SET)
  {
  }

protected:
  bool force_systemverilog = false;
  bool vl2smv_extensions = false;
  bool warn_implicit_nets = false;
  bool ignore_initial = false;
  bool initial_zero = false;
  std::list<std::string> include_paths;
  std::list<std::string> initial_defines;
  verilog_parse_treet parse_tree;
};
 
std::unique_ptr<languaget> new_verilog_language();

#endif
