/*******************************************************************\

Module: Verilog Language Interface

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Verilog Language Interface

#include "verilog_ebmc_language.h"

#include <util/cmdline.h>
#include <util/get_module.h>
#include <util/unicode.h>

#include <ebmc/ebmc_error.h>
#include <ebmc/transition_system.h>

#include "verilog_parser.h"
#include "verilog_typecheck.h"

#include <fstream>

verilog_parse_treet verilog_ebmc_languaget::parse()
{
  verilog_standardt standard;

  verilog_parsert verilog_parser{standard, message_handler};

  auto file_name = verilog_file_name(cmdline);

  std::ifstream infile{widen_if_needed(file_name)};

  if(!infile)
    throw ebmc_errort{} << "failed to open " << file_name;

  verilog_parser.set_file(file_name);
  verilog_parser.in = &infile;

  if(verilog_parser.parse())
    throw ebmc_errort{} << "parsing has failed";

  return std::move(verilog_parser.parse_tree);
}

std::optional<transition_systemt> verilog_ebmc_languaget::transition_system()
{
  auto parse_tree = parse();

  transition_systemt result;

  if(verilog_typecheck(parse_tree, result.symbol_table, "main", message_handler))
    throw ebmc_errort{} << "typechecking has failed";

  result.main_symbol =
    &get_module(result.symbol_table, "main", message_handler);

  result.trans_expr =
    to_trans_expr(result.main_symbol->value);

  return result;
}
