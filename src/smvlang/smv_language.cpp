/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smv_language.h"

#include <util/namespace.h>
#include <util/symbol_table.h>

#include "expr2smv.h"
#include "smv_parser.h"
#include "smv_typecheck.h"

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
  smv_parse_treet::modulest::const_iterator
    m_it=smv_parse_tree.modules.find(module);

  if(m_it==smv_parse_tree.modules.end()) return;

  const smv_parse_treet::modulet &smv_module=m_it->second;

  for(smv_parse_treet::mc_varst::const_iterator it=smv_module.vars.begin();
      it!=smv_module.vars.end(); it++)
    if(it->second.type.id()=="submodule")
      module_set.insert(it->second.type.get_string("identifier"));
}

/*******************************************************************\

Function: smv_languaget::modules_provided

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smv_languaget::modules_provided(std::set<std::string> &module_set)
{
  for(smv_parse_treet::modulest::const_iterator
      it=smv_parse_tree.modules.begin();
      it!=smv_parse_tree.modules.end(); it++)
    module_set.insert(id2string(it->second.name));
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
  for(smv_parse_treet::modulest::const_iterator
      it=smv_parse_tree.modules.begin();
      it!=smv_parse_tree.modules.end(); it++)
  {
    const smv_parse_treet::modulet &module=it->second;
    out << "Module: " << module.name << std::endl << std::endl;

    out << "  PARAMETERS:\n";

    for(auto &parameter : module.parameters)
      out << "    " << parameter << '\n';

    out << '\n';

    out << "  VARIABLES:" << std::endl;

    for(smv_parse_treet::mc_varst::const_iterator it=module.vars.begin();
        it!=module.vars.end(); it++)
      if(it->second.type.id()!="submodule")
      {
        symbol_tablet symbol_table;
        namespacet ns{symbol_table};
        auto msg = type2smv(it->second.type, ns);
        out << "    " << it->first << ": " << msg << ";\n";
      }

    out << std::endl;

    out << "  SUBMODULES:" << std::endl;

    for(smv_parse_treet::mc_varst::const_iterator
        it=module.vars.begin();
        it!=module.vars.end(); it++)
      if(it->second.type.id()=="submodule")
      {
        symbol_tablet symbol_table;
        namespacet ns(symbol_table);
        auto msg = type2smv(it->second.type, ns);
        out << "    " << it->first << ": " << msg << ";\n";
      }

    out << std::endl;

    out << "  ITEMS:" << std::endl;

    forall_item_list(it, module.items)
    {
      out << "    TYPE: " << to_string(it->item_type) << std::endl;
      out << "    EXPR: " << it->expr.pretty() << std::endl;
      out << std::endl;
    }
  }
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

