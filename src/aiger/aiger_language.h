/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_AIGER_LANGUAGE_H
#define CPROVER_AIGER_LANGUAGE_H

#include <util/options.h>

#include <langapi/language.h>

class aiger_languaget:public languaget
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

  ~aiger_languaget() override { }
  
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
    return std::make_unique<aiger_languaget>();
  }

  std::string id() const override { return "AIGER"; }
  std::string description() const override { return "AIGER"; }

  std::set<std::string> extensions() const override
  { 
    return { "aig" };
  }

  aiger_languaget()
  {
  }
};
 
std::unique_ptr<languaget> new_aiger_language();

#endif
