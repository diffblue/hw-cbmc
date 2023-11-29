/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SMV_LANGUAGE_H
#define CPROVER_SMV_LANGUAGE_H

/*! \defgroup gr_smvlang SMV front-end */

#include <langapi/language.h>

#include "smv_parse_tree.h"

/*! \brief TO_BE_DOCUMENTED
    \ingroup gr_smvlang
*/
class smv_languaget:public languaget
{
public:
  bool parse(
    std::istream &instream,
    const std::string &path) override;

  void dependencies(
    const std::string &module,
    std::set<std::string> &module_set) override;

  void modules_provided(
    std::set<std::string> &module_set) override;

  bool typecheck(symbol_table_baset &symbol_table, const std::string &module)
    override;

  void show_parse(std::ostream &out) override;
  
  ~smv_languaget() override { }
  
  bool from_expr(
    const exprt &expr,
    std::string &code,
    const namespacet &ns) override;

  bool from_type(
    const typet &type,
    std::string &code,
    const namespacet &ns) override;

  bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &expr,
    const namespacet &ns) override;

  bool generate_support_functions(symbol_table_baset &) override
  {
    return false;
  }

  std::string id() const override { return "SMV"; }
  std::string description() const override { return "SMV"; }

  std::set<std::string> extensions() const override
  {
    return { "smv" }; 
  }
  
  std::unique_ptr<languaget> new_language() override
  {
    return std::make_unique<smv_languaget>();
  }

  smv_parse_treet smv_parse_tree;
};

std::unique_ptr<languaget> new_smv_language();
 
#endif
