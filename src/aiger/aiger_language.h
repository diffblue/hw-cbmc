/*******************************************************************\

Module: AIGER Language Registration

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_AIGER_LANGUAGE_H
#define CPROVER_AIGER_LANGUAGE_H

#include <langapi/language.h>

/// Minimal languaget for AIGER, used for language mode registration
/// (from_expr, from_type). The actual front-end is aiger_ebmc_languaget.
class aiger_languaget : public languaget
{
public:
  bool preprocess(
    std::istream &,
    const std::string &,
    std::ostream &,
    message_handlert &) override
  {
    return true;
  }

  bool parse(std::istream &, const std::string &, message_handlert &) override
  {
    return true;
  }

  void dependencies(const std::string &, std::set<std::string> &) override
  {
  }

  void modules_provided(std::set<std::string> &) override
  {
  }

  bool interfaces(symbol_table_baset &, message_handlert &) override
  {
    return false;
  }

  bool typecheck(symbol_table_baset &, const std::string &, message_handlert &)
    override
  {
    return true;
  }

  void show_parse(std::ostream &, message_handlert &) override
  {
  }

  bool from_expr(const exprt &, std::string &, const namespacet &) override;
  bool from_type(const typet &, std::string &, const namespacet &) override;

  bool to_expr(
    const std::string &,
    const std::string &,
    exprt &,
    const namespacet &,
    message_handlert &) override
  {
    return true;
  }

  bool
  generate_support_functions(symbol_table_baset &, message_handlert &) override
  {
    return false;
  }

  std::unique_ptr<languaget> new_language() override
  {
    return std::make_unique<aiger_languaget>();
  }

  std::string id() const override
  {
    return "AIGER";
  }

  std::string description() const override
  {
    return "AIGER";
  }

  std::set<std::string> extensions() const override
  {
    return {"aig", "aag"};
  }
};

std::unique_ptr<languaget> new_aiger_language();

#endif // CPROVER_AIGER_LANGUAGE_H
