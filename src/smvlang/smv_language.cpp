/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smv_language.h"

#include <util/namespace.h>
#include <util/symbol_table.h>

#include "expr2smv.h"
#include "smv_expr.h"
#include "smv_parser.h"
#include "smv_typecheck.h"
#include "smv_types.h"

/*******************************************************************\

Function: smv_languaget::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool smv_languaget::parse(
  std::istream &instream,
  const std::string &path,
  message_handlert &message_handler)
{
  smv_parsert smv_parser(message_handler);

  smv_parser.set_file(path);
  smv_parser.in=&instream;

  bool result=smv_parser.parse();

  smv_parse_tree.swap(smv_parser.parse_tree);

  return result;
}

/*******************************************************************\

Function: smv_languaget::dependencies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_languaget::dependencies(
  const std::string &module, 
  std::set<std::string> &module_set)
{
}

/*******************************************************************\

Function: smv_languaget::modules_provided

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_languaget::modules_provided(std::set<std::string> &module_set)
{
  for(const auto &module : smv_parse_tree.module_list)
    module_set.insert(id2string(module.identifier));
}

/*******************************************************************\

Function: smv_languaget::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool smv_languaget::typecheck(
  symbol_table_baset &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
{
  return smv_typecheck(smv_parse_tree, symbol_table, module, message_handler);
}

/*******************************************************************\

Function: smv_languaget::show_parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_languaget::show_parse(std::ostream &out, message_handlert &)
{
  smv_parse_tree.show(out);
}

/*******************************************************************\

Function: smv_languaget::from_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool smv_languaget::from_expr(const exprt &expr, std::string &code,
                              const namespacet &ns)
{
  code = expr2smv(expr, ns);
  return false;
}

/*******************************************************************\

Function: smv_languaget::from_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool smv_languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns)
{
  code = type2smv(type, ns);
  return false;
}

/*******************************************************************\

Function: smv_languaget::to_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool smv_languaget::to_expr(
  const std::string &code,
  const std::string &module,
  exprt &,
  const namespacet &,
  message_handlert &message_handler)
{
  messaget message(message_handler);
  message.error() << "not yet implemented" << messaget::eom;
  return true;
}

/*******************************************************************\

Function: new_smv_language

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
std::unique_ptr<languaget> new_smv_language()
{
  return std::make_unique<smv_languaget>();
}

