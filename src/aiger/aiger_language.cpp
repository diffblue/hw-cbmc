/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "aiger_language.h"

#include <util/message.h>

/*******************************************************************\

Function: aiger_languaget::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool aiger_languaget::parse(
  std::istream &,
  const std::string &,
  message_handlert &)
{
  return true;
}

/*******************************************************************\

Function: aiger_languaget::preprocess

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool aiger_languaget::preprocess(
  std::istream &,
  const std::string &,
  std::ostream &,
  message_handlert &message_handler)
{
  messaget message(message_handler);
  message.error() << "there is no AIGER preprocessing" << messaget::eom;
  return true;
}

/*******************************************************************\

Function: aiger_languaget::dependencies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void aiger_languaget::dependencies(
  const std::string &module,
  std::set<std::string> &module_set)
{
}

/*******************************************************************\

Function: aiger_languaget::modules_provided

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void aiger_languaget::modules_provided(
  std::set<std::string> &module_set)
{
}
             
/*******************************************************************\

Function: aiger_languaget::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool aiger_languaget::typecheck(
  symbol_table_baset &,
  const std::string &,
  message_handlert &)
{
  return true;
}

/*******************************************************************\

Function: aiger_languaget::interfaces

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool aiger_languaget::interfaces(symbol_table_baset &, message_handlert &)
{
  return false;
}

/*******************************************************************\

Function: aiger_languaget::show_parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void aiger_languaget::show_parse(std::ostream &, message_handlert &)
{
}

/*******************************************************************\

Function: aiger_languaget::from_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool aiger_languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  return true;
}

/*******************************************************************\

Function: aiger_languaget::from_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool aiger_languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns)
{
  return true;
}

/*******************************************************************\

Function: aiger_languaget::to_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool aiger_languaget::to_expr(
  const std::string &code,
  const std::string &module,
  exprt &,
  const namespacet &,
  message_handlert &)
{
  return true;
}

/*******************************************************************\

Function: new_aiger_language

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
std::unique_ptr<languaget> new_aiger_language()
{
  return std::make_unique<aiger_languaget>();
}

