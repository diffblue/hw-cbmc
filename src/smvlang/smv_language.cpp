/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smv_language.h"
#include "smv_typecheck.h"
#include "smv_parser.h"
#include "expr2smv.h"

/*******************************************************************\

Function: smv_languaget::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool smv_languaget::parse(
  std::istream &instream,
  const std::string &path)
{
  smv_parser.clear();

  const std::string main_name=smv_module_symbol("main");
  smv_parser.module=&smv_parser.parse_tree.modules[main_name];
  smv_parser.module->name=main_name;
  smv_parser.module->base_name="main";

  smv_parser.set_file(path);
  smv_parser.in=&instream;
  smv_parser.set_message_handler(get_message_handler());

  bool result=smv_parser.parse();

  // see if we used main

  if(!smv_parser.parse_tree.modules[main_name].used)
    smv_parser.parse_tree.modules.erase(main_name);

  smv_parse_tree.swap(smv_parser.parse_tree);

  // save some memory
  smv_parser.clear();

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
  symbol_tablet &symbol_table,
  const std::string &module)
{
  return smv_typecheck(smv_parse_tree, symbol_table, module,
                       get_message_handler());
}

/*******************************************************************\

Function: smv_languaget::show_parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
void smv_languaget::show_parse(std::ostream &out)
{
  for(smv_parse_treet::modulest::const_iterator
      it=smv_parse_tree.modules.begin();
      it!=smv_parse_tree.modules.end(); it++)
  {
    const smv_parse_treet::modulet &module=it->second;
    out << "Module: " << module.name << std::endl << std::endl;

    out << "  VARIABLES:" << std::endl;

    for(smv_parse_treet::mc_varst::const_iterator it=module.vars.begin();
        it!=module.vars.end(); it++)
      if(it->second.type.id()!="submodule")
      {
        std::string msg;
        type2smv(it->second.type, msg);
        out << "    " << it->first << ": " 
            << msg << ";" << std::endl;
      }

    out << std::endl;

    out << "  SUBMODULES:" << std::endl;

    for(smv_parse_treet::mc_varst::const_iterator
        it=module.vars.begin();
        it!=module.vars.end(); it++)
      if(it->second.type.id()=="submodule")
      {
        std::string msg;
        type2smv(it->second.type, msg);
        out << "    " << it->first << ": " 
            << msg << ";" << std::endl;
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
  return expr2smv(expr, code);
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
  return type2smv(type, code);
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
  exprt &expr,
  const namespacet &ns)
{
  error() << "not yet implemented" << eom;
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
  return util_make_unique<smv_languaget>();
}

