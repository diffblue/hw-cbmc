/*******************************************************************\

Module: SMV Language Interface

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// SMV Language Interface

#include "smv_ebmc_language.h"

#include <util/cmdline.h>
#include <util/get_module.h>
#include <util/unicode.h>

#include <ebmc/ebmc_error.h>
#include <ebmc/transition_system.h>

#include "smv_parser.h"
#include "smv_typecheck.h"

#include <fstream>
#include <iostream>

std::string smv_file_name(const cmdlinet &cmdline)
{
  if(cmdline.args.size() == 0)
    throw ebmc_errort{} << "no file name given";

  if(cmdline.args.size() >= 2)
    throw ebmc_errort{}.with_exit_code(1) << "SMV only uses a single file";

  return cmdline.args.front();
}

smv_parse_treet smv_ebmc_languaget::parse()
{
  smv_parsert smv_parser{message_handler};

  auto file_name = smv_file_name(cmdline);

  std::ifstream infile{widen_if_needed(file_name)};

  if(!infile)
    throw ebmc_errort{}.with_exit_code(1) << "failed to open " << file_name;

  smv_parser.set_file(file_name);
  smv_parser.in = &infile;

  if(smv_parser.parse())
    throw ebmc_errort{}.with_exit_code(1);

  return std::move(smv_parser.parse_tree);
}

std::optional<transition_systemt> smv_ebmc_languaget::transition_system()
{
  if(cmdline.isset("preprocess"))
  {
    throw ebmc_errort{}.with_exit_code(1) << "SMV does not use preprocessing";
  }

  auto parse_tree = parse();

  if(cmdline.isset("show-parse"))
  {
    parse_tree.show(std::cout);
    return {};
  }

  if(cmdline.isset("show-modules"))
  {
    std::size_t count = 0;
    auto &out = std::cout;

    for(const auto &module : parse_tree.module_list)
    {
      count++;

      out << "Module " << count << ":" << '\n';

      out << "  Location:   " << module.source_location << '\n';
      out << "  Identifier: " << module.name << '\n';
      out << "  Name:       " << module.base_name << '\n' << '\n';
    }

    return {};
  }

  if(cmdline.isset("modules-xml") || cmdline.isset("json-modules"))
  {
    //show_modules(cmdline, message_handler);
    return {};
  }

  if(cmdline.isset("show-module-hierarchy"))
  {
    //show_module_hierarchy(cmdline, message_handler);
    return {};
  }

  transition_systemt result;

  if(smv_typecheck(
       parse_tree, result.symbol_table, "smv::main", message_handler))
  {
    messaget message{message_handler};
    message.error() << "CONVERSION ERROR" << messaget::eom;
    throw ebmc_errort{}.with_exit_code(2);
  }

  if(cmdline.isset("show-symbol-table"))
  {
    std::cout << result.symbol_table;
    return {};
  }

  result.main_symbol =
    &get_module(result.symbol_table, "main", message_handler);

  result.trans_expr = to_trans_expr(result.main_symbol->value);

  return result;
}
