/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "aiger_language.h"

#include <util/message.h>
#include <util/prefix.h>

#include <sstream>

/*******************************************************************\

Function: aiger_languaget::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool aiger_languaget::parse(
  std::istream &in,
  const std::string &file_path,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  // The first line is "aig M I L O A", where
  // the capital letters are placeholders for nonnegative decimal
  // numbers.
  std::string line;
  if(!std::getline(in, line))
  {
    message.error() << "failed to read AIGER header" << messaget::eom;
    return true;
  }

  std::istringstream line_stream(line);  
  std::string format_identifier;
  auto &M = parse_tree.M,
       &I = parse_tree.I,
       &L = parse_tree.L,
       &O = parse_tree.O,
       &A = parse_tree.A;

  if(!(line_stream >> format_identifier >> M >> I >> L >> O >> A))
  {
    message.error() << "failed to parse AIGER header" << messaget::eom;
    return true;
  }

  if(format_identifier != "aig")
  {
    message.error() << "unexpected AIGER format identifier" << messaget::eom;
    return true;
  }

  // The header is followed by L next-state literals,
  // one per line
  std::vector<literalt> next_state_literals;
  next_state_literals.reserve(L);

  for(std::size_t i = 0; i < L; i++)
  {
    if(!std::getline(in, line))
    {
      message.error() << "failed to read AIGER next-state literal line" << messaget::eom;
      return true;
    }

    std::size_t l = std::strtoull(line);
    if(next_state_literal == 0)
    {
      message.error() << "failed to parse AIGER next-state literal line" << messaget::eom;
      return true;
    }

    next_state_literals.emplace_back(l >> 1, l & 1);
  }

  // Then we have O output literals, one per line
  std::vector<literalt> output_literals;
  output_literals.reserve(L);

  for(std::size_t i = 0; i < O; i++)
  {
    if(!std::getline(in, line))
    {
      message.error() << "failed to read AIGER output literal line" << messaget::eom;
      return true;
    }

    std::size_t l = std::strtoull(line);
    if(next_state_literal == 0)
    {
      message.error() << "failed to parse AIGER output literal line" << messaget::eom;
      return true;
    }

    output_literals.emplace_back(l >> 1, l & 1);
  }

  // Now we have, in differential binary, the AND gates

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
  // AIGER files never have dependencies
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
  // AIGER files do not have modules
}
             
/*******************************************************************\

Function: aiger_languaget::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool aiger_languaget::typecheck(
  symbol_table_baset &symbol_table,
  const std::string &, // module name
  message_handlert &message_handler)
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

