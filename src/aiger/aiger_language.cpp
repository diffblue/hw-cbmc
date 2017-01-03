/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "aiger_language.h"

/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "aiger_language.h"

/*******************************************************************\

Function: aiger_languaget::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool aiger_languaget::parse(
  std::istream &instream,
  const std::string &path)
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
  std::istream &instream,
  const std::string &path,
  std::ostream &outstream)
{
  error() << "there is no AIGER preprocessing" << eom;
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
  symbol_tablet &symbol_table,
  const std::string &module)
{
  return true;
}

/*******************************************************************\

Function: aiger_languaget::interfaces

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool aiger_languaget::interfaces(
  symbol_tablet &symbol_table)
{
  return false;
}

/*******************************************************************\

Function: aiger_languaget::show_parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
void aiger_languaget::show_parse(std::ostream &out)
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
  exprt &expr,
  const namespacet &ns)
{
  return true;
}

/*******************************************************************\

Function: new_aiger_language

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
languaget *new_aiger_language()
{
  return new aiger_languaget;
}

