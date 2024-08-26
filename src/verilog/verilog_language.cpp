/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <sstream>

#include <util/suffix.h>
#include <util/symbol_table.h>

#include "verilog_language.h"
#include "verilog_typecheck.h"
#include "verilog_synthesis.h"
#include "expr2verilog.h"
#include "verilog_parser.h"
#include "verilog_preprocessor.h"

/*******************************************************************\

Function: verilog_languaget::set_language_options

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_languaget::set_language_options(
  const optionst &options,
  message_handlert &message_handler)
{
  force_systemverilog = options.get_bool_option("force-systemverilog");
  vl2smv_extensions = options.get_bool_option("vl2smv-extensions");
  initial_defines = options.get_list_option("defines");
}

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
  std::stringstream str;

  if(preprocess(instream, path, str, message_handler))
    return true;

  verilog_standardt standard;

  if(has_suffix(path, ".sv") || force_systemverilog)
    standard = verilog_standardt::SV2023;
  else if(vl2smv_extensions)
    standard = verilog_standardt::V2005_SMV;
  else
    standard = verilog_standardt::V2005_SMV;

  verilog_parsert verilog_parser(standard, message_handler);

  verilog_parser.set_file(path);
  verilog_parser.in=&str;
  verilog_parser.grammar=verilog_parsert::LANGUAGE;

  verilog_scanner_init();

  bool result=verilog_parser.parse();

  parse_tree.swap(verilog_parser.parse_tree);

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
  verilog_preprocessort preprocessor(
    instream, outstream, message_handler, path, initial_defines);

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

    const auto &module = *it->second;

    for(auto &identifier : module.submodules())
      module_set.insert(id2string(identifier));
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
  symbol_table_baset &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
{
  if(module=="") return false;

  if(verilog_typecheck(parse_tree, symbol_table, module, message_handler))
    return true;

  messaget message(message_handler);
  message.debug() << "Synthesis " << module << messaget::eom;

  if(verilog_synthesis(
       symbol_table, module, parse_tree.standard, message_handler, optionst{}))
    return true;

  return false;
}

/*******************************************************************\

Function: verilog_languaget::interfaces

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_languaget::interfaces(symbol_table_baset &, message_handlert &)
{
  return false;
}

/*******************************************************************\

Function: verilog_languaget::show_parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_languaget::show_parse(std::ostream &out, message_handlert &)
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
  code = expr2verilog(expr, ns);
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
  code = type2verilog(type, ns);
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
  const namespacet &ns,
  message_handlert &message_handler)
{
  expr.make_nil();
  
  // no preprocessing yet...

  std::istringstream i_preprocessed(code);

  verilog_standardt standard = verilog_standardt::V2005;

  // parsing
  verilog_parsert verilog_parser(standard, message_handler);

  verilog_parser.set_file("");
  verilog_parser.in=&i_preprocessed;
  verilog_parser.grammar=verilog_parsert::EXPRESSION;
  verilog_scanner_init();

  bool result=verilog_parser.parse();
  if(result) return true;

  expr.swap(verilog_parser.parse_tree.expr);

  // typecheck it
  result = verilog_typecheck(expr, module, standard, message_handler, ns);
  if(result)
    return true;

  // synthesize it
  result = verilog_synthesis(expr, module, standard, message_handler, ns);
  if(result)
    return true;

  return result;
}

/*******************************************************************\

Function: new_verilog_language

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
std::unique_ptr<languaget> new_verilog_language()
{
  return std::make_unique<verilog_languaget>();
}

