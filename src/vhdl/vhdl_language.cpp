/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/suffix.h>
#include <util/symbol_table.h>

#include "vhdl_language.h"
#include "vhdl_typecheck.h"
#include "vhdl_synthesis.h"
#include "vhdl_std_packages.h"
#include "expr2vhdl.h"
#include "vhdl_parser.h"

/*******************************************************************\

Function: vhdl_languaget::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool vhdl_languaget::parse(
  std::istream &instream,
  const std::string &path,
  message_handlert &message_handler)
{
  vhdl_parsert vhdl_parser(message_handler);

  vhdl_parser.set_file(path);
  vhdl_parser.in=&instream;
  //vhdl_parser.grammar=vhdl_parsert::LANGUAGE;
  
  vhdl_scanner_init();

  bool result=vhdl_parser.parse();

  parse_tree.swap(vhdl_parser.parse_tree);

  return result;
}

/*******************************************************************\

Function: vhdl_languaget::preprocess

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool vhdl_languaget::preprocess(
  std::istream &,
  const std::string &,
  std::ostream &,
  message_handlert &message_handler)
{
  messaget message(message_handler);
  message.error() << "there is no VHDL preprocessing" << messaget::eom;
  return true;
}

/*******************************************************************\

Function: vhdl_languaget::dependencies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_languaget::dependencies(
  const std::string &module,
  std::set<std::string> &module_set)
{
  #if 0
  vhdl_parse_treet::module_mapt::const_iterator it=
    parse_tree.module_map.find(
      id2string(vhdl_module_name(module)));

  if(it!=parse_tree.module_map.end())
  {
    // dependencies on other Verilog modules
    
    const vhdl_modulet &module=(it->second)->vhdl_module;
 
    forall_irep(it2, module.module_items.get_sub())
    {
      if(it2->id()==ID_inst)
        module_set.insert(
          id2string(vhdl_module_symbol(it2->get_string(ID_module))));
    }
  }
  #endif
}

/*******************************************************************\

Function: vhdl_languaget::modules_provided

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_languaget::modules_provided(
  std::set<std::string> &module_set)
{
  for(auto const &i : parse_tree.items)
  {
    if(i.is_architecture())
    {
      module_set.insert(
        vhdl_parse_treet::itemt::pretty_name(i.get_name()));
    }
  }
}
             
/*******************************************************************\

Function: vhdl_languaget::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool vhdl_languaget::typecheck(
  symbol_table_baset &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
{
  if(module=="") return false;

  vhdl_std_packages(symbol_table, message_handler);

  if(vhdl_typecheck(parse_tree, symbol_table, module, message_handler))
    return true;

  messaget message(message_handler);
  message.debug() << "Synthesis" << messaget::eom;

  std::string module2="vhdl::"+module;

  if(vhdl_synthesis(symbol_table, module2, message_handler))
    return true;

  return false;
}

/*******************************************************************\

Function: vhdl_languaget::interfaces

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool vhdl_languaget::interfaces(symbol_table_baset &, message_handlert &)
{
  return false;
}

/*******************************************************************\

Function: vhdl_languaget::show_parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_languaget::show_parse(std::ostream &out, message_handlert &)
{
  parse_tree.show(out);
}

/*******************************************************************\

Function: vhdl_languaget::from_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool vhdl_languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  code=expr2vhdl(expr);
  return false;
}

/*******************************************************************\

Function: vhdl_languaget::from_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool vhdl_languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns)
{
  code=type2vhdl(type);
  return false;
}

/*******************************************************************\

Function: vhdl_languaget::to_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool vhdl_languaget::to_expr(
  const std::string &code,
  const std::string &module,
  exprt &expr,
  const namespacet &ns,
  message_handlert &message_handler)
{
  expr.make_nil();
  
  // no preprocessing
  std::istringstream i_preprocessed(code);

  // parsing
  vhdl_parsert vhdl_parser(message_handler);
  vhdl_parser.set_file("");
  vhdl_parser.in=&i_preprocessed;
  vhdl_parser.grammar=vhdl_parsert::EXPRESSION;
  vhdl_scanner_init();

  bool result=vhdl_parser.parse();
  if(result) return true;

  //expr.swap(vhdl_parser.parse_tree.expr);

  #if 0
  // typecheck it
  result=vhdl_typecheck(expr, module, message_handler, ns);
  #endif

  return result;
}

/*******************************************************************\

Function: new_vhdl_language

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
std::unique_ptr<languaget> new_vhdl_language()
{
  return std::make_unique<vhdl_languaget>();
}

