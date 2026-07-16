/*******************************************************************\

Module: Main Module

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "hw_cbmc_parse_options.h"

#include <util/cmdline.h>
#include <util/config.h>
#include <util/ebmc_util.h>
#include <util/exit_codes.h>
#include <util/find_symbols.h>
#include <util/get_module.h>
#include <util/invariant.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/string2int.h>
#include <util/unicode.h>
#include <util/version.h>

#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/show_symbol_table.h>

#include <ansi-c/goto-conversion/goto_convert_functions.h>
#include <ebmc/show_modules.h>
#include <ebmc/transition_system.h>
#include <goto-checker/all_properties_verifier_with_trace_storage.h>
#include <goto-checker/goto_verifier.h>
#include <goto-checker/multi_path_symex_checker.h>
#include <langapi/language_file.h>
#include <langapi/mode.h>
#include <linking/static_lifetime_init.h>
#include <trans-word-level/instantiate_word_level.h>
#include <trans-word-level/trans_trace_word_level.h>
#include <trans-word-level/unwind.h>
#include <verilog/verilog_ebmc_language.h>

#include "gen_interface.h"
#include "map_vars.h"

#include <iostream>

/*******************************************************************\

Function: is_verilog_file

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static bool is_verilog_file(const std::string &file_name)
{
  const auto extension = std::filesystem::path(file_name).extension().string();
  return extension == ".v" || extension == ".sv";
}

/*******************************************************************\

Function: disable_default_hw_cbmc_checks

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void
disable_default_hw_cbmc_checks(const cmdlinet &cmdline, optionst &options)
{
  // This restores the defaults that hw-cbmc used to have,
  // as opposed to the new defaults that came with cbmc 6.0.
  // This will be removed eventually.

  if(!cmdline.isset("bounds-check") && !cmdline.isset("no-bounds-check"))
    options.set_option("bounds-check", false);

  if(!cmdline.isset("pointer-check") && !cmdline.isset("no-pointer-check"))
    options.set_option("pointer-check", false);

  if(
    !cmdline.isset("pointer-primitive-check") &&
    !cmdline.isset("no-pointer-primitive-check"))
  {
    options.set_option("pointer-primitive-check", false);
  }

  if(
    !cmdline.isset("div-by-zero-check") &&
    !cmdline.isset("no-div-by-zero-check"))
  {
    options.set_option("div-by-zero-check", false);
  }

  if(
    !cmdline.isset("signed-overflow-check") &&
    !cmdline.isset("no-signed-overflow-check"))
  {
    options.set_option("signed-overflow-check", false);
  }

  if(
    !cmdline.isset("undefined-shift-check") &&
    !cmdline.isset("no-undefined-shift-check"))
  {
    options.set_option("undefined-shift-check", false);
  }

  if(
    !cmdline.isset("unwinding-assertions") &&
    !cmdline.isset("no-unwinding-assertions"))
  {
    options.set_option("unwinding-assertions", false);
    options.set_option("paths-symex-explore-all", false);
  }

  config.ansi_c.malloc_may_fail = false;
  config.ansi_c.malloc_failure_mode =
    configt::ansi_ct::malloc_failure_modet::malloc_failure_mode_none;
}

/*******************************************************************\

Function: merge_symbol_tables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void merge_symbol_tables(
  symbol_table_baset &dest,
  const symbol_tablet &src,
  message_handlert &message_handler)
{
  messaget log(message_handler);

  for(const auto &entry : src)
  {
    auto insert_result = dest.insert(entry.second);
    if(!insert_result.second)
    {
      log.error() << "failed to merge symbol `" << entry.first << "'"
                  << messaget::eom;
      throw 0;
    }
  }
}

/*******************************************************************\

Function: get_hw_cbmc_entry_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static symbolt &get_hw_cbmc_entry_function(
  symbol_table_baset &symbol_table,
  const optionst &options,
  message_handlert &message_handler)
{
  irep_idt entry_function = ID_main;

  if(options.is_set("function"))
    entry_function = options.get_option("function");
  else if(config.main.has_value())
    entry_function = *config.main;

  auto matches = symbol_table.match_name_or_base_name(entry_function);

  for(auto it = matches.begin(); it != matches.end();)
  {
    if((*it)->second.type.id() != ID_code || (*it)->second.is_property)
      it = matches.erase(it);
    else
      ++it;
  }

  messaget log(message_handler);

  if(matches.empty())
  {
    log.error() << "entry function `" << entry_function << "' not found"
                << messaget::eom;
    throw 0;
  }

  if(matches.size() >= 2)
  {
    log.error() << "entry function `" << entry_function << "' is ambiguous"
                << messaget::eom;
    throw 0;
  }

  return symbol_table.get_writeable_ref(matches.front()->first);
}

/*******************************************************************\

Function: build_hw_cbmc_assumptions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static code_blockt build_hw_cbmc_assumptions(
  const symbol_table_baset &symbol_table,
  const irep_idt &unwind_module,
  const unsigned unwind_no_timeframes,
  const std::list<exprt> &constraints)
{
  code_blockt assumptions;

  for(const auto &entry : symbol_table)
  {
    const auto &symbol = entry.second;

    if(symbol.value.id() != ID_index)
      continue;

    const auto &index_expr = to_index_expr(symbol.value);
    if(index_expr.array().id() != ID_symbol)
      continue;

    const auto &array_identifier =
      to_symbol_expr(index_expr.array()).get_identifier();
    if(array_identifier != id2string(symbol.name) + "_array")
      continue;

    mp_integer index_value;
    if(
      to_integer_non_constant(index_expr.index(), index_value) ||
      index_value != 0)
    {
      continue;
    }

    assumptions.add(
      code_assumet(equal_exprt(symbol.symbol_expr(), symbol.value)));
  }

  if(!unwind_module.empty() && unwind_no_timeframes != 0)
  {
    const namespacet ns(symbol_table);
    const symbolt &symbol = ns.lookup(unwind_module);
    const transt &trans = to_trans_expr(symbol.value);

    if(!trans.invar().is_true())
    {
      for(std::size_t timeframe = 0; timeframe < unwind_no_timeframes;
          ++timeframe)
      {
        assumptions.add(code_assumet(
          instantiate(trans.invar(), timeframe, unwind_no_timeframes)));
      }
    }

    if(!trans.init().is_true())
    {
      assumptions.add(
        code_assumet(instantiate(trans.init(), 0, unwind_no_timeframes)));
    }

    if(!trans.trans().is_true())
    {
      for(std::size_t timeframe = 0; timeframe < unwind_no_timeframes;
          ++timeframe)
      {
        assumptions.add(code_assumet(
          instantiate(trans.trans(), timeframe, unwind_no_timeframes)));
      }
    }
  }

  for(const auto &constraint : constraints)
    assumptions.add(code_assumet(constraint));

  return assumptions;
}

/*******************************************************************\

Function: add_timeframe_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void add_timeframe_symbols(
  symbol_table_baset &symbol_table,
  const code_blockt &assumptions)
{
  find_symbols_sett identifiers;

  for(const auto &statement : assumptions.statements())
    find_symbols(statement, identifiers);

  for(const auto &identifier : identifiers)
  {
    if(symbol_table.has_symbol(identifier))
      continue;

    const std::string identifier_string = id2string(identifier);
    const auto separator_pos = identifier_string.rfind('@');
    if(separator_pos == std::string::npos)
      continue;

    const irep_idt base_identifier = identifier_string.substr(0, separator_pos);
    if(!symbol_table.has_symbol(base_identifier))
      continue;

    symbolt symbol = symbol_table.lookup_ref(base_identifier);
    symbol.name = identifier;
    symbol.base_name = identifier;
    symbol.pretty_name = identifier;
    symbol.is_static_lifetime = true;
    symbol.is_lvalue = true;
    symbol.value = nondet_symbol_exprt(identifier, symbol.type);

    (void)symbol_table.insert(std::move(symbol));
  }
}

/*******************************************************************\

Function: instrument_entry_function_with_assumptions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void instrument_entry_function_with_assumptions(
  symbol_table_baset &symbol_table,
  const optionst &options,
  message_handlert &message_handler,
  const irep_idt &unwind_module,
  const unsigned unwind_no_timeframes,
  const std::list<exprt> &constraints)
{
  code_blockt assumptions = build_hw_cbmc_assumptions(
    symbol_table, unwind_module, unwind_no_timeframes, constraints);

  if(assumptions.operands().empty())
    return;

  add_timeframe_symbols(symbol_table, assumptions);

  symbolt &entry_function =
    get_hw_cbmc_entry_function(symbol_table, options, message_handler);

  PRECONDITION(entry_function.value.id() == ID_code);

  code_blockt instrumented_body;
  for(const auto &statement : assumptions.statements())
    instrumented_body.add(statement);
  instrumented_body.add(to_code(entry_function.value));
  entry_function.value = std::move(instrumented_body);
}

/*******************************************************************\

Function: hw_cbmc_parse_optionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int hw_cbmc_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << std::endl;
    return CPROVER_EXIT_SUCCESS;
  }

  //
  // command line options
  //

  optionst options;
  get_command_line_options(options);
  disable_default_hw_cbmc_checks(cmdline, options);

  messaget::eval_verbosity(cmdline.get_value("verbosity"),
                           messaget::M_STATISTICS, ui_message_handler);

  if(cmdline.isset("vcd"))
    options.set_option("vcd", cmdline.get_value("vcd"));

  //
  // Print a banner
  //
  log.status() << "HW-CBMC version " << CBMC_VERSION << messaget::eom;

  register_languages();

  if(cmdline.isset("preprocess"))
  {
    preprocessing(options);
    return CPROVER_EXIT_SUCCESS;
  }

  if(cmdline.args.empty())
  {
    log.error() << "Please provide a program to verify" << messaget::eom;
    return CPROVER_EXIT_INCORRECT_TASK;
  }

  std::list<std::string> binaries, sources;
  std::vector<std::string> verilog_sources;

  for(const auto &arg : cmdline.args)
  {
    if(is_goto_binary(arg, ui_message_handler))
      binaries.push_back(arg);
    else if(is_verilog_file(arg))
      verilog_sources.push_back(arg);
    else
      sources.push_back(arg);
  }

  language_filest language_files;

  initialize_from_source_files(
    sources,
    options,
    language_files,
    goto_model.symbol_table,
    ui_message_handler);

  if(read_objects_and_link(binaries, goto_model, ui_message_handler))
    return CPROVER_EXIT_INTERNAL_ERROR;

  set_up_custom_entry_point(
    language_files,
    goto_model.symbol_table,
    [this](const irep_idt &identifier)
    { return goto_model.unload(identifier); },
    options,
    true,
    ui_message_handler);

  if(language_files.final(goto_model.symbol_table))
  {
    log.error() << "FINAL STAGE CONVERSION ERROR" << messaget::eom;
    return CPROVER_EXIT_INCORRECT_TASK;
  }

  if(!verilog_sources.empty())
  {
    cmdlinet verilog_cmdline = cmdline;
    verilog_cmdline.args.assign(verilog_sources.begin(), verilog_sources.end());

    verilog_ebmc_languaget verilog_language(
      verilog_cmdline, ui_message_handler);
    auto transition_system = verilog_language.transition_system();

    if(!transition_system.has_value())
      return CPROVER_EXIT_SUCCESS;

    merge_symbol_tables(
      goto_model.symbol_table,
      transition_system->symbol_table,
      ui_message_handler);
  }

  std::list<exprt> constraints;

  int get_modules_ret = get_modules(constraints);
  if(get_modules_ret != -1)
    return get_modules_ret;

  unwind_no_timeframes = get_bound();
  unwind_module = get_top_module();

  if(!constraints.empty() || !unwind_module.empty())
  {
    log.status() << "Encoding hardware constraints" << messaget::eom;
    instrument_entry_function_with_assumptions(
      goto_model.symbol_table,
      options,
      ui_message_handler,
      unwind_module,
      unwind_no_timeframes,
      constraints);
  }

  if(cmdline.isset("show-symbol-table"))
  {
    show_symbol_table(goto_model.symbol_table, ui_message_handler);
    return CPROVER_EXIT_SUCCESS;
  }

  goto_convert(
    goto_model.symbol_table, goto_model.goto_functions, ui_message_handler);

  recreate_initialize_function(goto_model, ui_message_handler);

  update_max_malloc_size(goto_model, ui_message_handler);

  if(cbmc_parse_optionst::process_goto_program(goto_model, options, log))
    return CPROVER_EXIT_INTERNAL_ERROR;

  if(cmdline.isset("validate-goto-model"))
    goto_model.validate();

  if(cmdline.isset("show-loops"))
  {
    show_loop_ids(ui_message_handler.get_ui(), goto_model);
    return CPROVER_EXIT_SUCCESS;
  }

  if(
    cmdline.isset("show-goto-functions") ||
    cmdline.isset("list-goto-functions"))
  {
    show_goto_functions(
      goto_model, ui_message_handler, cmdline.isset("list-goto-functions"));
    return CPROVER_EXIT_SUCCESS;
  }

  label_properties(goto_model.goto_functions);

  if(cmdline.isset("show-properties"))
  {
    show_properties(goto_model, ui_message_handler);
    return CPROVER_EXIT_SUCCESS;
  }

  if(set_properties())
    return CPROVER_EXIT_SET_PROPERTIES_FAILED;

  std::unique_ptr<goto_verifiert> verifier = std::make_unique<
    all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>>(
    options, ui_message_handler, goto_model);

  // do actual BMC
  const resultt result = (*verifier)();
  verifier->report();

  return result_to_exit_code(result);
}

/*******************************************************************\

Function: hw_cbmc_parse_optionst::get_top_module

  Inputs:

 Outputs:

 Purpose: add additional (synchonous) modules

\*******************************************************************/

irep_idt hw_cbmc_parse_optionst::get_top_module()
{
  std::string top_module;

  if(cmdline.isset("module"))
    top_module=cmdline.get_value("module");
  else if(cmdline.isset("top"))
    top_module=cmdline.get_value("top");

  if(top_module=="")
    return irep_idt();

  return get_module(goto_model.symbol_table, top_module, ui_message_handler)
      .name;
}

/*******************************************************************\

Function: hw_cbmc_parse_optionst::get_bound

  Inputs:

 Outputs:

 Purpose: add additional (synchonous) modules

\*******************************************************************/

unsigned hw_cbmc_parse_optionst::get_bound()
{
  if(cmdline.isset("bound"))
    return safe_string2unsigned(cmdline.get_value("bound"))+1;
  else
    return 1;
}

/*******************************************************************\

Function: hw_cbmc_parse_optionst::get_modules

  Inputs:

 Outputs:

 Purpose: add additional (synchonous) modules

\*******************************************************************/

int hw_cbmc_parse_optionst::get_modules(std::list<exprt> &bmc_constraints) {
  //
  // unwinding of transition systems
  //

  irep_idt top_module=get_top_module();

  if(!top_module.empty())
  {
    try
    {
      if(cmdline.isset("gen-interface"))
      {
        const symbolt &symbol =
            namespacet(goto_model.symbol_table).lookup(top_module);

        if(cmdline.isset("outfile"))
        {
          std::ofstream out(widen_if_needed(cmdline.get_value("outfile")));
          if(!out)
          {
            log.error() << "failed to open given outfile" << messaget::eom;
            return CPROVER_EXIT_INCORRECT_TASK;
          }

          gen_interface(goto_model.symbol_table, symbol, true, out, std::cerr);
        }
        else
          gen_interface(goto_model.symbol_table, symbol, true, std::cout, std::cerr);

        return CPROVER_EXIT_SUCCESS; // done
      }

      //
      // map HDL variables to C variables
      //

      log.status() << "Mapping variables" << messaget::eom;

      map_vars(goto_model.symbol_table, top_module, bmc_constraints,
               ui_message_handler, get_bound());
    }

    catch(int e)
    {
      return CPROVER_EXIT_EXCEPTION;
    }
  }
  else if(cmdline.isset("gen-interface"))
  {
    log.error() << "must specify top module name for gen-interface"
                << messaget::eom;
    return CPROVER_EXIT_INCORRECT_TASK;
  }
  else if(cmdline.isset("show-modules"))
  {
    show_modulest::from_symbol_table(goto_model.symbol_table)
      .plain_text(std::cout);
    return CPROVER_EXIT_SUCCESS; // done
  }

  return -1; // continue
}

/*******************************************************************\

Function: hw_cbmc_parse_optionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void hw_cbmc_parse_optionst::help()
{
  std::cout <<
    "* *  hw-cbmc is protected in part by U.S. patent 7,225,417  * *";

  cbmc_parse_optionst::help();

  std::cout <<
    "hw-cbmc also accepts the following options:\n"
    " --module name                top module for unwinding (deprecated)\n"
    " --top name                   top module for unwinding\n"
    " --bound nr                   number of transitions for the module\n"
    " --gen-interface              print C for interface to module\n"
    " --vcd file                   dump error trace in VCD format\n"
    "\n";
}

void hw_cbmc_parse_optionst::do_unwind_module(prop_convt &prop_conv) {
  if (unwind_module == "" || unwind_no_timeframes == 0)
    return;

  namespacet ns{goto_model.symbol_table};
  const symbolt &symbol = ns.lookup(unwind_module);

  log.status() << "Unwinding transition system `" << symbol.name << "' with "
               << unwind_no_timeframes << " time frames" << messaget::eom;

  //  auto dp= get_decision_procedure();

  ::unwind(to_trans_expr(symbol.value), ui_message_handler, prop_conv,
           unwind_no_timeframes, ns, true);

  log.status() << "Unwinding transition system done" << messaget::eom;
}

void hw_cbmc_parse_optionst::show_unwind_trace(const optionst &options,
                                               const prop_convt &prop_conv) {
  if (unwind_module == "" || unwind_no_timeframes == 0)
    return;

  namespacet ns{goto_model.symbol_table};
  auto trans_trace =
    compute_trans_trace(prop_conv, unwind_no_timeframes, ns, unwind_module);

  if (options.get_option("vcd") != "") {
    if (options.get_option("vcd") == "-")
      show_trans_trace_vcd(trans_trace, log, ns, std::cout);
    else {
      std::ofstream out(widen_if_needed(options.get_option("vcd")));
      show_trans_trace_vcd(trans_trace, log, ns, out);
    }
  }

  switch(ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    show_trans_trace(trans_trace, log, ns, std::cout);
    break;

  case ui_message_handlert::uit::XML_UI:
    show_trans_trace_xml(trans_trace, log, ns, std::cout);
    break;

  case ui_message_handlert::uit::JSON_UI:
    show_trans_trace_json(trans_trace, log, ns, std::cout);
    break;
  }
}
