/*******************************************************************\

Module: VHDL Language Interface

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// VHDL Language Interface

#include "vhdl_ebmc_language.h"

#include <util/cmdline.h>
#include <util/get_module.h>
#include <util/output_file.h>
#include <util/unicode.h>

#include <ebmc/ebmc_error.h>
#include <ebmc/show_modules.h>
#include <ebmc/transition_system.h>

#include "vhdl_parser.h"
#include "vhdl_synthesis.h"
#include "vhdl_typecheck.h"

#include <fstream>
#include <iostream>

void vhdl_ebmc_languaget::parse(
  const std::filesystem::path &path,
  vhdl_parse_treet &parse_tree)
{
  std::ifstream infile{path};

  if(!infile)
    throw ebmc_errort{}.with_exit_code(1) << "failed to open " << path;

  vhdl_parsert vhdl_parser{message_handler};

  vhdl_parser.set_file(path.u8string());
  vhdl_parser.in = &infile;
  vhdl_parser.grammar = vhdl_parsert::LANGUAGE;

  vhdl_scanner_init();

  if(vhdl_parser.parse())
    throw ebmc_errort{}.with_exit_code(1);

  parse_tree.items.splice(parse_tree.items.end(), vhdl_parser.parse_tree.items);
}

vhdl_parse_treet vhdl_ebmc_languaget::parse()
{
  vhdl_parse_treet parse_tree;

  for(auto &arg : cmdline.args)
    parse(widen_if_needed(arg), parse_tree);

  return parse_tree;
}

irep_idt
vhdl_ebmc_languaget::top_level_entity(const vhdl_parse_treet &parse_tree)
{
  std::optional<irep_idt> top;

  if(cmdline.isset("module"))
    top = cmdline.get_value("module");
  else if(cmdline.isset("top"))
    top = cmdline.get_value("top");

  // VHDL identifiers are case insensitive; we use lower case
  if(top.has_value())
    top = vhdl_parse_treet::itemt::to_lower(*top);

  std::vector<irep_idt> entities;

  for(auto &item : parse_tree.items)
    if(item.is_entity())
      entities.push_back(item.get_identifier());

  if(top.has_value())
  {
    for(auto &entity : entities)
      if(entity == *top)
        return entity;

    throw ebmc_errort{} << "entity `" << *top << "' not found";
  }

  if(entities.empty())
    throw ebmc_errort{} << "no entity found";

  if(entities.size() >= 2)
    throw ebmc_errort{} << "multiple entities found, please use --top";

  return entities.front();
}

std::optional<transition_systemt> vhdl_ebmc_languaget::transition_system()
{
  if(cmdline.isset("preprocess"))
  {
    throw ebmc_errort{}.with_exit_code(1) << "VHDL does not use preprocessing";
  }

  auto parse_tree = parse();

  if(cmdline.isset("show-parse"))
  {
    parse_tree.show(std::cout);
    return {};
  }

  if(
    cmdline.isset("show-modules") || cmdline.isset("modules-xml") ||
    cmdline.isset("json-modules"))
  {
    show_modulest show_modules;

    for(const auto &item : parse_tree.items)
      if(item.is_entity())
      {
        auto identifier = item.get_identifier();
        show_modules.modules.emplace_back(
          "vhdl::" + id2string(identifier),
          identifier,
          "VHDL",
          item.source_location());
      }

    if(cmdline.isset("show-modules"))
      show_modules.plain_text(std::cout);
    else if(cmdline.isset("modules-xml"))
    {
      output_filet output_file{cmdline.get_value("modules-xml")};
      show_modules.xml(output_file.stream());
    }
    else if(cmdline.isset("json-modules"))
    {
      output_filet output_file{cmdline.get_value("json-modules")};
      show_modules.json(output_file.stream());
    }

    return {};
  }

  auto top = top_level_entity(parse_tree);

  messaget message{message_handler};
  message.status() << "Converting " << top << messaget::eom;

  transition_systemt result;

  const std::string module_identifier = "vhdl::" + id2string(top);

  if(vhdl_typecheck(
       parse_tree, result.symbol_table, id2string(top), message_handler))
  {
    message.error() << "CONVERSION ERROR" << messaget::eom;
    throw ebmc_errort{}.with_exit_code(2);
  }

  if(vhdl_synthesis(result.symbol_table, module_identifier, message_handler))
  {
    message.error() << "CONVERSION ERROR" << messaget::eom;
    throw ebmc_errort{}.with_exit_code(2);
  }

  if(cmdline.isset("show-symbol-table"))
  {
    std::cout << result.symbol_table;
    return {};
  }

  result.main_symbol =
    &get_module(result.symbol_table, id2string(top), message_handler);

  result.trans_expr = to_trans_expr(result.main_symbol->value);

  return result;
}
