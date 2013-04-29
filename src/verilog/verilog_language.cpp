/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <sstream>

#include <util/suffix.h>

#include "verilog_language.h"
#include "verilog_typecheck.h"
#include "verilog_synthesis.h"
#include "expr2verilog.h"
#include "verilog_parser.h"
#include "verilog_preprocessor.h"

/*******************************************************************\

Function: verilog_languaget::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_languaget::parse(
  std::istream &instream,
  const std::string &path,
  message_handlert &message_handler)
{
  verilog_parser.clear();

  std::stringstream str;

  if(preprocess(instream, path, str, message_handler))
    return true;

  verilog_parser.filename=path;
  verilog_parser.in=&str;
  verilog_parser.set_message_handler(message_handler);
  verilog_parser.grammar=verilog_parsert::LANGUAGE;
  
  if(has_suffix(path, ".sv"))
    verilog_parser.mode=verilog_parsert::SYSTEM_VERILOG;

  verilog_scanner_init();

  bool result=verilog_parser.parse();

  parse_tree.swap(verilog_parser.parse_tree);

  // save some memory
  verilog_parser.clear();

  return result;
}

/*******************************************************************\

Function: verilog_languaget::preprocess

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_languaget::preprocess(
  std::istream &instream,
  const std::string &path,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  std::stringstream str;

  verilog_preprocessort preprocessor(
    instream, outstream, message_handler, path);

  try { preprocessor.preprocessor(); }
  catch(int e) { return true; }

  return false;
}

/*******************************************************************\

Function: verilog_languaget::dependencies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_languaget::dependencies(
  const std::string &module,
  std::set<std::string> &module_set)
{
  verilog_parse_treet::module_mapt::const_iterator it=
    parse_tree.module_map.find(
      id2string(verilog_module_name(module)));

  if(it!=parse_tree.module_map.end())
  {
    // dependencies on other Verilog modules
    
    const verilog_modulet &module=(it->second)->verilog_module;
 
    forall_irep(it2, module.module_items.get_sub())
    {
      if(it2->id()==ID_inst)
        module_set.insert(
          id2string(verilog_module_symbol(it2->get_string(ID_module))));
    }
  }
}

/*******************************************************************\

Function: verilog_languaget::modules_provided

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_languaget::modules_provided(
  std::set<std::string> &module_set)
{
  parse_tree.modules_provided(module_set);
}
             
/*******************************************************************\

Function: verilog_languaget::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_languaget::typecheck(
  symbol_tablet &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
{
  if(module=="") return false;

  if(verilog_typecheck(parse_tree, symbol_table, module, message_handler))
    return true;
    
  message_handler.print(9, "Synthesis "+module);

  if(verilog_synthesis(symbol_table, module, message_handler, options))
    return true;

  return false;
}

/*******************************************************************\

Function: verilog_languaget::interfaces

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_languaget::interfaces(
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  return false;
}

/*******************************************************************\

Function: verilog_languaget::show_parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
void verilog_languaget::show_parse(std::ostream &out)
{
  parse_tree.show(out);
}

/*******************************************************************\

Function: verilog_languaget::from_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  code=expr2verilog(expr);
  return false;
}

/*******************************************************************\

Function: verilog_languaget::from_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns)
{
  code=type2verilog(type);
  return false;
}

/*******************************************************************\

Function: verilog_languaget::to_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_languaget::to_expr(
  const std::string &code,
  const std::string &module,
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &ns)
{
  expr.make_nil();
  
  // no preprocessing yet...

  std::istringstream i_preprocessed(code);

  // parsing
  
  verilog_parser.clear();
  verilog_parser.filename="";
  verilog_parser.in=&i_preprocessed;
  verilog_parser.set_message_handler(message_handler);
  verilog_parser.grammar=verilog_parsert::EXPRESSION;
  verilog_scanner_init();

  bool result=verilog_parser.parse();
  if(result) return true;

  expr.swap(verilog_parser.parse_tree.expr);

  // typecheck it
  result=verilog_typecheck(expr, module, message_handler, ns);

  // save some memory
  verilog_parser.clear();

  return result;
}

/*******************************************************************\

Function: new_verilog_language

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
languaget *new_verilog_language()
{
  return new verilog_languaget;
}

