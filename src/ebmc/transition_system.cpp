/*******************************************************************\

Module: Transition Systems for EBMC

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "transition_system.h"

#include <util/cmdline.h>
#include <util/config.h>
#include <util/get_module.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/unicode.h>

#include <langapi/language.h>
#include <langapi/language_file.h>
#include <langapi/language_util.h>
#include <langapi/mode.h>
#include <trans-word-level/show_module_hierarchy.h>
#include <trans-word-level/show_modules.h>

#include "ebmc_error.h"
#include "ebmc_version.h"

#include <fstream>
#include <iostream>

static void output(
  const exprt &expr,
  std::ostream &out,
  languaget &language,
  const namespacet &ns)
{
  if(expr.id() == ID_and)
  {
    for(auto &conjunct : expr.operands())
      output(conjunct, out, language, ns);
  }
  else
  {
    std::string text;

    if(language.from_expr(expr, text, ns))
    {
      throw ebmc_errort() << "failed to convert expression";
    }

    out << "  " << text << '\n' << '\n';
  }
}

void transition_systemt::output(std::ostream &out) const
{
  auto language = get_language_from_mode(main_symbol->mode);

  const namespacet ns{symbol_table};

  out << "Initial state constraints:\n\n";

  ::output(trans_expr.init(), out, *language, ns);

  out << "State constraints:\n\n";

  ::output(trans_expr.invar(), out, *language, ns);

  out << "Transition constraints:\n\n";

  ::output(trans_expr.trans(), out, *language, ns);
}

int preprocess(const cmdlinet &cmdline, message_handlert &message_handler)
{
  messaget message(message_handler);

  if(cmdline.args.size() != 1)
  {
    message.error() << "please give exactly one file to preprocess"
                    << messaget::eom;
    return 1;
  }

  const auto &filename = cmdline.args.front();
  std::ifstream infile(widen_if_needed(filename));

  if(!infile)
  {
    message.error() << "failed to open input file `" << filename << "'"
                    << messaget::eom;
    return 1;
  }

  // do -I
  if(cmdline.isset('I'))
    config.verilog.include_paths = cmdline.get_values('I');

  auto language = get_language_from_filename(filename);

  if(language == nullptr)
  {
    source_locationt location;
    location.set_file(filename);
    message.error().source_location = location;
    message.error() << "failed to figure out type of file" << messaget::eom;
    return 1;
  }

  language->set_message_handler(message_handler);

  if(language->preprocess(infile, filename, std::cout))
  {
    message.error() << "PREPROCESSING FAILED" << messaget::eom;
    return 1;
  }

  return 0;
}

bool parse(
  const std::string &filename,
  language_filest &language_files,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  std::ifstream infile(widen_if_needed(filename));

  if(!infile)
  {
    message.error() << "failed to open input file `" << filename << "'"
                    << messaget::eom;
    return true;
  }

  auto &lf = language_files.add_file(filename);
  lf.filename = filename;
  lf.language = get_language_from_filename(filename);

  if(lf.language == nullptr)
  {
    source_locationt location;
    location.set_file(filename);
    message.error().source_location = location;
    message.error() << "failed to figure out type of file" << messaget::eom;
    return true;
  }

  languaget &language = *lf.language;
  language.set_message_handler(message_handler);

  message.status() << "Parsing " << filename << messaget::eom;

  if(language.parse(infile, filename))
  {
    message.error() << "PARSING ERROR\n";
    return true;
  }

  lf.get_modules();

  return false;
}

bool parse(
  const cmdlinet &cmdline,
  language_filest &language_files,
  message_handlert &message_handler)
{
  for(unsigned i = 0; i < cmdline.args.size(); i++)
  {
    if(parse(cmdline.args[i], language_files, message_handler))
      return true;
  }
  return false;
}

bool get_main(
  const cmdlinet &cmdline,
  message_handlert &message_handler,
  transition_systemt &transition_system)
{
  std::string top_module;

  if(cmdline.isset("module"))
    top_module = cmdline.get_value("module");
  else if(cmdline.isset("top"))
    top_module = cmdline.get_value("top");

  try
  {
    transition_system.main_symbol =
      &get_module(transition_system.symbol_table, top_module, message_handler);
    transition_system.trans_expr =
      to_trans_expr(transition_system.main_symbol->value);
  }

  catch(int e)
  {
    return true;
  }

  return false;
}

void make_next_state(exprt &expr)
{
  for(auto &sub_expression : expr.operands())
    make_next_state(sub_expression);

  if(expr.id() == ID_symbol)
    expr.id(ID_next_symbol);
}

int get_transition_system(
  const cmdlinet &cmdline,
  message_handlert &message_handler,
  transition_systemt &transition_system)
{
  messaget message(message_handler);

  // do -I
  if(cmdline.isset('I'))
    config.verilog.include_paths = cmdline.get_values('I');

  if(cmdline.isset("preprocess"))
    return preprocess(cmdline, message_handler);

  //
  // parsing
  //
  language_filest language_files;

  if(parse(cmdline, language_files, message_handler))
    return 1;

  if(cmdline.isset("show-parse"))
  {
    language_files.show_parse(std::cout);
    return 0;
  }

  //
  // type checking
  //

  message.status() << "Converting" << messaget::eom;

  if(language_files.typecheck(transition_system.symbol_table, message_handler))
  {
    message.error() << "CONVERSION ERROR" << messaget::eom;
    return 2;
  }

  if(cmdline.isset("show-modules"))
  {
    show_modules(transition_system.symbol_table, std::cout);
    return 0;
  }

  if(cmdline.isset("modules-xml"))
  {
    auto filename = cmdline.get_value("modules-xml");
    std::ofstream out(widen_if_needed(filename));
    if(!out)
      throw ebmc_errort() << "failed to open " << filename;
    show_modules_xml(transition_system.symbol_table, out);
    return 0;
  }

  if(cmdline.isset("show-symbol-table"))
  {
    std::cout << transition_system.symbol_table;
    return 0;
  }

  // get module name

  if(get_main(cmdline, message_handler, transition_system))
    return 1;

  if(cmdline.isset("show-module-hierarchy"))
  {
    DATA_INVARIANT(
      transition_system.main_symbol != nullptr, "must have main_symbol");
    show_module_hierarchy(
      transition_system.symbol_table,
      *transition_system.main_symbol,
      std::cout);
    return 0;
  }

  // --reset given?
  if(cmdline.isset("reset"))
  {
    namespacet ns(transition_system.symbol_table);
    exprt reset_constraint = to_expr(
      ns, transition_system.main_symbol->name, cmdline.get_value("reset"));

    // true in initial state
    transt new_trans_expr = transition_system.trans_expr;
    new_trans_expr.init() = and_exprt(new_trans_expr.init(), reset_constraint);

    // and not anymore afterwards
    exprt reset_next_state = reset_constraint;
    make_next_state(reset_next_state);

    new_trans_expr.trans() =
      and_exprt(new_trans_expr.trans(), not_exprt(reset_next_state));
    transition_system.trans_expr = new_trans_expr;
  }

  return -1; // done with the transition system
}

transition_systemt get_transition_system(
  const cmdlinet &cmdline,
  message_handlert &message_handler)
{
  transition_systemt transition_system;
  auto exit_code =
    get_transition_system(cmdline, message_handler, transition_system);
  if(exit_code != -1)
    throw ebmc_errort().with_exit_code(exit_code);
  return transition_system;
}

int show_parse(const cmdlinet &cmdline, message_handlert &message_handler)
{
  transition_systemt dummy_transition_system;
  return get_transition_system(
    cmdline, message_handler, dummy_transition_system);
}

int show_modules(const cmdlinet &cmdline, message_handlert &message_handler)
{
  transition_systemt dummy_transition_system;
  return get_transition_system(
    cmdline, message_handler, dummy_transition_system);
}

int show_module_hierarchy(
  const cmdlinet &cmdline,
  message_handlert &message_handler)
{
  transition_systemt dummy_transition_system;
  return get_transition_system(
    cmdline, message_handler, dummy_transition_system);
}

int show_symbol_table(
  const cmdlinet &cmdline,
  message_handlert &message_handler)
{
  transition_systemt dummy_transition_system;
  return get_transition_system(
    cmdline, message_handler, dummy_transition_system);
}
