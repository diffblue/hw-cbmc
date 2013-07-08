/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <sstream>

#include <util/suffix.h>

#include "vhdl_language.h"
#include "vhdl_typecheck.h"
#include "vhdl_synthesis.h"
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
  vhdl_parser.clear();

  vhdl_parser.set_file(path);
  vhdl_parser.in=&instream;
  vhdl_parser.set_message_handler(message_handler);
  //vhdl_parser.grammar=vhdl_parsert::LANGUAGE;
  
  //if(has_suffix(path, ".sv"))
  //  vhdl_parser.mode=vhdl_parsert::SYSTEM_VERILOG;

  vhdl_scanner_init();

  bool result=vhdl_parser.parse();

  parse_tree.swap(vhdl_parser.parse_tree);

  // save some memory
  vhdl_parser.clear();

  return result;
}

/*******************************************************************\

Function: vhdl_languaget::preprocess

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool vhdl_languaget::preprocess(
  std::istream &instream,
  const std::string &path,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  messaget message(message_handler);
  message.error("there is no VHDL preprocessing");
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
  #if 0
  parse_tree.modules_provided(module_set);
  #endif
}
             
/*******************************************************************\

Function: vhdl_languaget::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool vhdl_languaget::typecheck(
  symbol_tablet &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
{
  if(module=="") return false;

  #if 0
  if(vhdl_typecheck(parse_tree, symbol_table, module, message_handler))
    return true;
    
  message_handler.print(9, "Synthesis");

  if(vhdl_synthesis(symbol_table, module, message_handler, options))
    return true;
  #endif

  return false;
}

/*******************************************************************\

Function: vhdl_languaget::interfaces

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool vhdl_languaget::interfaces(
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  return false;
}

/*******************************************************************\

Function: vhdl_languaget::show_parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
void vhdl_languaget::show_parse(std::ostream &out)
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
  message_handlert &message_handler,
  const namespacet &ns)
{
  expr.make_nil();
  
  // no preprocessing
  std::istringstream i_preprocessed(code);

  // parsing
  
  vhdl_parser.clear();
  vhdl_parser.set_file("");
  vhdl_parser.in=&i_preprocessed;
  vhdl_parser.set_message_handler(message_handler);
  vhdl_parser.grammar=vhdl_parsert::EXPRESSION;
  vhdl_scanner_init();

  bool result=vhdl_parser.parse();
  if(result) return true;

  expr.swap(vhdl_parser.parse_tree.expr);

  #if 0
  // typecheck it
  result=vhdl_typecheck(expr, module, message_handler, ns);
  #endif

  // save some memory
  vhdl_parser.clear();

  return result;
}

/*******************************************************************\

Function: new_vhdl_language

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
languaget *new_vhdl_language()
{
  return new vhdl_languaget;
}

