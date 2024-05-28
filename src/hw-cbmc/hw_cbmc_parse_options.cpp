/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "hw_cbmc_parse_options.h"

#include <util/config.h>
#include <util/exit_codes.h>
#include <util/get_module.h>
#include <util/string2int.h>
#include <util/unicode.h>
#include <util/version.h>

#include <goto-programs/set_properties.h>
#include <goto-programs/show_properties.h>

#include <ansi-c/goto-conversion/goto_convert_functions.h>
#include <goto-checker/all_properties_verifier_with_trace_storage.h>
#include <goto-checker/goto_verifier.h>
#include <goto-checker/multi_path_symex_checker.h>
#include <goto-checker/solver_factory.h>
#include <langapi/mode.h>
#include <trans-word-level/show_modules.h>
#include <trans-word-level/trans_trace_word_level.h>
#include <trans-word-level/unwind.h>

#include "gen_interface.h"
#include "map_vars.h"

#include <iostream>

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
    return 0;
  }

  //
  // command line options
  //

  optionst options;
  get_command_line_options(options);

  messaget::eval_verbosity(cmdline.get_value("verbosity"),
                           messaget::M_STATISTICS, ui_message_handler);

  //
  // Print a banner
  //
  log.status() << "HW-CBMC version " << CBMC_VERSION << messaget::eom;

  register_languages();

  if(cmdline.isset("preprocess"))
  {
    preprocessing(options);
    return 0;
  }

  if(cmdline.isset("vcd"))
    options.set_option("vcd", cmdline.get_value("vcd"));

  std::unique_ptr<goto_verifiert> verifier = nullptr;
  verifier = std::make_unique<
    all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>>(
    options, ui_message_handler, goto_model);

  // TODO : implement custom goto-checker/verifier that would support
  // do-unwind-module and add-constraints (see below)

  int get_goto_program_ret =
      get_goto_program(goto_model, options, cmdline, ui_message_handler);
  if (get_goto_program_ret != -1)
    return get_goto_program_ret;

  std::list<exprt> constraints;
  int get_modules_ret = get_modules(constraints);
  if (get_modules_ret != -1)
    return get_modules_ret;

  goto_convert(goto_model.symbol_table, goto_model.goto_functions,
               ui_message_handler);
  if (cbmc_parse_optionst::process_goto_program(goto_model, options, log))
    return CPROVER_EXIT_INTERNAL_ERROR;

  unwind_no_timeframes = get_bound();
  unwind_module = get_top_module();

  // TODO : reimplement `do_module_unwind` inside the new custom verifier

  // the 'extra constraints'
  if (!constraints.empty()) {
    log.status() << "converting constraints" << messaget::eom;

    for (const auto &constraint : constraints) {
      // TODO : include the extra constraints using the new custom verifier
      // interface
      (void)constraint;
    }
  }

  label_properties(goto_model.goto_functions);

  if (cmdline.isset("show-properties")) {
    show_properties(goto_model, ui_message_handler);
    return 0;
  }
  if (set_properties())
    return 7;

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
            return 6;
          }

          gen_interface(goto_model.symbol_table, symbol, true, out, std::cerr);
        }
        else
          gen_interface(goto_model.symbol_table, symbol, true, std::cout, std::cerr);

        return 0; // done
      }
      
      //
      // map HDL variables to C variables
      //

      log.status() << "Mapping variables" << messaget::eom;

      map_vars(goto_model.symbol_table, top_module, bmc_constraints,
               ui_message_handler, get_bound());
    }

    catch(int e) { return 6; }
  }
  else if(cmdline.isset("gen-interface"))
  {
    log.error() << "must specify top module name for gen-interface"
                << messaget::eom;
    return 6;
  }
  else if(cmdline.isset("show-modules"))
  {
    show_modules(goto_model.symbol_table, std::cout);
    return 0; // done
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
