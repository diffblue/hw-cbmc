/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ebmc_parse_options.h"

#include <util/config.h>
#include <util/exit_codes.h>
#include <util/help_formatter.h>
#include <util/string2int.h>

#include <trans-netlist/smv_netlist.h>

#include "diatest.h"
#include "ebmc_base.h"
#include "ebmc_error.h"
#include "ebmc_version.h"
#include "format_hooks.h"
#include "instrument_buechi.h"
#include "liveness_to_safety.h"
#include "netlist.h"
#include "neural_liveness.h"
#include "output_file.h"
#include "output_smv_word_level.h"
#include "property_checker.h"
#include "random_traces.h"
#include "ranking_function.h"
#include "show_properties.h"
#include "show_trans.h"

#include <iostream>

#include "cegar/bmc_cegar.h"

#ifdef HAVE_INTERPOLATION
#include "interpolation/interpolation_expr.h"
#include "interpolation/interpolation_netlist.h"
#include "interpolation/interpolation_netlist_vmcai.h"
#include "interpolation/interpolation_word.h"
#include "interpolation/compute-interpolant.h"
#include "coverage/coverage.h"
#endif

/*******************************************************************\

Function: ebmc_parse_optionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int ebmc_parse_optionst::doit()
{
  if(cmdline.isset("verbosity"))
    ui_message_handler.set_verbosity(
      unsafe_string2unsigned(cmdline.get_value("verbosity")));
  else
    ui_message_handler.set_verbosity(messaget::M_STATUS); // default

  if(config.set(cmdline))
  {
    usage_error();
    return CPROVER_EXIT_USAGE_ERROR;
  }

  register_languages();
  format_hooks();

  if(cmdline.isset("version"))
  {
    std::cout << EBMC_VERSION << '\n';
    return 0;
  }

  try
  {
    if(cmdline.isset("diatest"))
    {
      if(!cmdline.isset("statebits"))
        throw ebmc_errort() << "must provide number of state bits";

      auto statebits_opt =
        string2optional_size_t(cmdline.get_value("statebits"));

      if(!statebits_opt.has_value())
        throw ebmc_errort() << "failed to parse number of state bits";

      if(!cmdline.isset("bound"))
        throw ebmc_errort() << "must provide bound";

      auto bound_opt = string2optional_size_t(cmdline.get_value("bound"));

      if(!bound_opt.has_value())
        throw ebmc_errort() << "failed to parse bound";

      diatest(*bound_opt, *statebits_opt, ui_message_handler);

      return 0;
    }

    if(cmdline.isset("preprocess"))
      return preprocess(cmdline, ui_message_handler);

    if(cmdline.isset("show-parse"))
      return show_parse(cmdline, ui_message_handler);

    if(
      cmdline.isset("show-modules") || cmdline.isset("modules-xml") ||
      cmdline.isset("json-modules"))
      return show_modules(cmdline, ui_message_handler);

    if(cmdline.isset("show-module-hierarchy"))
      return show_module_hierarchy(cmdline, ui_message_handler);

    if(cmdline.isset("show-symbol-table"))
      return show_symbol_table(cmdline, ui_message_handler);

    if(cmdline.isset("coverage"))
    {
      throw ebmc_errort() << "This option is currently disabled";

#if 0
      std::cout << "found coverage\n";
      //    return do_coverage(cmdline);
      //    if(do_coverage)
      //    {
        coveraget coverage(cmdline);
        return coverage.measure_coverage();
      //    }
#endif
    }

    if(cmdline.isset("random-traces"))
      return random_traces(cmdline, ui_message_handler);

    if(cmdline.isset("random-trace") || cmdline.isset("random-waveform"))
      return random_trace(cmdline, ui_message_handler);

    if(cmdline.isset("neural-liveness"))
      return do_neural_liveness(cmdline, ui_message_handler);

    if(cmdline.isset("ranking-function"))
      return do_ranking_function(cmdline, ui_message_handler);

    if(cmdline.isset("interpolation-word"))
    {
      throw ebmc_errort() << "This option is currently disabled";
      //#ifdef HAVE_INTERPOLATION
      //    return do_interpolation_word(cmdline);
      //#else
      //    language_uit language_ui("EBMC " EBMC_VERSION, cmdline);
      //    language_ui.error("No support for interpolation linked in");
      //    return 1;
      //#endif
    }

    if(cmdline.isset("interpolation-vmcai"))
    {
      throw ebmc_errort() << "This option is currently disabled";

      /*    #ifdef HAVE_INTERPOLATION
      return do_interpolation_netlist_vmcai(cmdline);
      #else
      language_uit language_ui(cmdline);
      language_ui.error("No support for interpolation linked in");
      return 1; 
      #endif
      */
    }

    if(cmdline.isset("interpolation"))
    {
#ifdef HAVE_INTERPOLATION
      //  if(cmdline.isset("no-netlist"))
      //      return do_interpolation(cmdline);
      //    else
      return do_interpolation_netlist(cmdline);
#else
      throw ebmc_errort() << "No support for interpolation linked in";
#endif
    }

    /*  if(cmdline.isset("compute-interpolant"))
    {
      #ifdef HAVE_INTERPOLATION
      return compute_interpolant(cmdline);
      #else
      language_uit language_ui(cmdline);
      language_ui.error("No support for interpolation linked in");
      return 1; 
      #endif
    }
    */

    if(cmdline.isset("2pi"))
    {
      // return do_two_phase_induction();
    }

    // get the transition system
    auto transition_system = get_transition_system(cmdline, ui_message_handler);

    // get the properties
    auto properties = ebmc_propertiest::from_command_line(
      cmdline, transition_system, ui_message_handler);

    if(cmdline.isset("show-properties"))
    {
      show_properties(properties, ui_message_handler);
      return 0;
    }

    if(cmdline.isset("json-properties"))
    {
      json_properties(properties, cmdline.get_value("json-properties"));
      return 0;
    }

    // LTL/SVA to Buechi?
    if(cmdline.isset("buechi"))
      instrument_buechi(transition_system, properties, ui_message_handler);

    // possibly apply liveness-to-safety
    if(cmdline.isset("liveness-to-safety"))
      liveness_to_safety(transition_system, properties);

    if(cmdline.isset("smv-word-level"))
    {
      auto filename = cmdline.value_opt("outfile").value_or("-");
      output_filet output_file{filename};
      output_smv_word_level(
        transition_system, properties, output_file.stream());
      return 0;
    }

    if(cmdline.isset("show-trans"))
    {
      auto filename = cmdline.value_opt("outfile").value_or("-");
      output_filet output_file{filename};
      return show_trans(transition_system, output_file.stream());
    }

    if(cmdline.isset("verilog-rtl"))
    {
      auto filename = cmdline.value_opt("outfile").value_or("-");
      output_filet output_file{filename};
      return show_trans_verilog_rtl(transition_system, output_file.stream());
    }

    if(cmdline.isset("verilog-netlist"))
    {
      auto filename = cmdline.value_opt("outfile").value_or("-");
      output_filet output_file{filename};
      return show_trans_verilog_netlist(
        transition_system, output_file.stream());
    }

    if(cmdline.isset("show-varmap"))
    {
      auto netlist =
        make_netlist(transition_system, properties, ui_message_handler);
      netlist.var_map.output(std::cout);
      return 0;
    }

    if(cmdline.isset("show-ldg"))
    {
      ebmc_baset ebmc_base(cmdline, ui_message_handler);
      ebmc_base.transition_system = std::move(transition_system);
      ebmc_base.properties = std::move(properties);
      ebmc_base.show_ldg(std::cout);
      return 0;
    }

    if(cmdline.isset("show-netlist"))
    {
      auto netlist =
        make_netlist(transition_system, properties, ui_message_handler);
      netlist.print(std::cout);
      return 0;
    }

    if(cmdline.isset("dot-netlist"))
    {
      auto netlist =
        make_netlist(transition_system, properties, ui_message_handler);
      auto filename = cmdline.value_opt("outfile").value_or("-");
      output_filet outfile{filename};
      outfile.stream() << "digraph netlist {\n";
      netlist.output_dot(outfile.stream());
      outfile.stream() << "}\n";
      return 0;
    }

    if(cmdline.isset("smv-netlist"))
    {
      auto netlist =
        make_netlist(transition_system, properties, ui_message_handler);
      auto filename = cmdline.value_opt("outfile").value_or("-");
      output_filet outfile{filename};
      outfile.stream() << "-- Generated by EBMC " << EBMC_VERSION << '\n';
      outfile.stream() << "-- Generated from "
                       << transition_system.main_symbol->name << '\n';
      outfile.stream() << '\n';
      smv_netlist(netlist, outfile.stream());
      return 0;
    }

    if(cmdline.isset("cegar"))
    {
      auto netlist =
        make_netlist(transition_system, properties, ui_message_handler);
      const namespacet ns(transition_system.symbol_table);
      return do_bmc_cegar(netlist, properties, ns, ui_message_handler);
    }

    if(cmdline.isset("compute-ct"))
    {
      ebmc_baset ebmc_base(cmdline, ui_message_handler);
      ebmc_base.transition_system = std::move(transition_system);
      ebmc_base.properties = std::move(properties);
      return ebmc_base.do_compute_ct();
    }

    auto checker_result = property_checker(
      cmdline, transition_system, properties, ui_message_handler);

    return checker_result.exit_code();
  }
  catch(const ebmc_errort &ebmc_error)
  {
    if(!ebmc_error.what().empty())
    {
      messaget message(ui_message_handler);
      if(ebmc_error.location().is_not_nil())
        message.error().source_location = ebmc_error.location();

      message.error() << "error: " << messaget::red << ebmc_error.what()
                      << messaget::reset << messaget::eom;
    }
    return ebmc_error.exit_code().value_or(CPROVER_EXIT_EXCEPTION);
  }
}

/*******************************************************************\

Function: ebmc_parse_optionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void ebmc_parse_optionst::help()
{
  std::cout
    << '\n'
    << banner_string("EBMC", EBMC_VERSION) << '\n'
    << "* *      EBMC - Copyright (C) 2001-2017 Daniel Kroening     * *\n"
       "* *     University of Oxford, Computer Science Department   * *\n"
       "* *                  kroening@kroening.com                  * *\n"
       "\n";

  std::cout << help_formatter(
    // clang-format off
    "Usage:\tPurpose:\n"
    "\n"
    " {bebmc} [{y-?}] [{y-h}] [{y--help}] \t show help\n"
    " {bebmc} {ufile} {u...}         \t source file names\n"
    "\n"
    "Additonal options:\n"
    " {y--bound} {unr}               \t set bound (default: 1)\n"
    " {y--module} {umodule}          \t set top module (deprecated)\n"
    " {y--top} {umodule}             \t set top module\n"
    " {y-p} {uexpr}                  \t specify a property\n"
    " {y--outfile} {ufile name}      \t set output file name (default: stdout)\n"
    " {y--json-result} {ufile name}  \t use JSON for property status and traces\n"
    " {y--trace}                     \t generate a trace for failing properties\n"
    " {y--vcd} {ufile name}          \t generate traces in VCD format\n"
    " {y--waveform}                  \t show a waveform for failing properties\n"
    " {y--numbered-trace}            \t give a trace with identifiers numbered by timeframe\n"
    " {y--show-properties}           \t list the properties in the model\n"
    " {y--property} {uid}            \t check the property with given ID\n"
    " {y--liveness-to-safety}        \t translate liveness properties to safety properties\n"
    " {y--buechi}                    \t translate LTL/SVA properties to Buechi acceptance\n"
    "\n"
    "Methods:\n"
    " {y--k-induction}               \t do k-induction with k=bound\n"
    " {y--bdd}                       \t use (unbounded) BDD engine\n"
    " {y--ic3}                       \t use IC3 engine with options described below\n"
    "    {y--constr}                 \t use constraints specified in 'file.cnstr'\n"
    "    {y--new-mode}               \t new mode is switched on\n"
    "    {y--aiger}                  \t print out the instance in aiger format\n"
    " {y--random-traces}             \t generate random traces\n"
    "    {y--traces} {unumber}       \t generate the given number of traces\n"
    "    {y--random-seed} {unumber}  \t use the given random seed\n"
    "    {y--trace-steps} {unumber}  \t set the number of random transitions (default: 10 steps)\n"
    " {y--random-trace}              \t generate a random trace\n"
    "    {y--random-seed} {unumber}  \t use the given random seed\n"
    "    {y--trace-steps} {unumber}  \t set the number of random transitions (default: 10 steps)\n"
    " {y--random-waveform}           \t generate a random trace and show it in horizontal form\n"
    "    {y--random-seed} {unumber}  \t use the given random seed\n"
    "    {y--trace-steps} {unumber}  \t set the number of random transitions (default: 10 steps)\n"
    " {y--ranking-function} {uf}     \t prove a liveness property using given ranking funnction (experimental)\n"
    "    {y--property} {uid}         \t the liveness property to prove\n"
    " {y--neural-liveness}           \t check liveness properties using neural "
                                       "inference (experimental)\n"
    "    {y--neural-engine} {ucmd}   \t the neural engine to use\n"

    //" --interpolation                \t use bit-level interpolants\n"
    //" --interpolation-word           \t use word-level interpolants\n"
    //" --diameter                     \t perform recurrence diameter test\n"
    "\n"
    "Solvers:\n"
    " {y--aig}                       \t bit-level SAT with AIGs\n"
    " {y--dimacs}                    \t output bit-level CNF in DIMACS format\n"
    " {y--smt2}                      \t output word-level SMT 2 formula\n"
    " {y--boolector}                 \t use Boolector as solver\n"
    " {y--cvc4}                      \t use CVC4 as solver\n"
    " {y--mathsat}                   \t use MathSAT as solver\n"
    " {y--yices}                     \t use Yices as solver\n"
    " {y--z3}                        \t use Z3 as solver\n"
    "\n"
    "Verilog options:\n"
    " {y-I} {upath}                  \t set include path\n"
    " {y-D} {uvar}[={uvalue}]        \t set preprocessor define\n"
    " {y--systemverilog}             \t force SystemVerilog instead of Verilog\n"
    " {y--reset} {uexpr}             \t set up module reset\n"
    " {y--ignore-initial}            \t disregard initial blocks\n"
    "\n"
    "Debugging options:\n"
    " {y--preprocess}                \t output the preprocessed source file\n"
    " {y--show-parse}                \t show parse trees\n"
    " {y--show-modules}              \t show a list of the modules\n"
    " {y--show-module-hierarchy}     \t show the hierarchy of module instantiations\n"
    " {y--show-varmap}               \t show variable map\n"
    " {y--show-netlist}              \t show netlist\n"
    " {y--show-ldg}                  \t show latch dependencies\n"
    " {y--show-formula}              \t show the formula that is generated\n"
    " {y--smv-netlist}               \t show netlist in SMV format\n"
    " {y--dot-netlist}               \t show netlist in DOT format\n"
    " {y--show-trans}                \t show transition system\n"
    " {y--smv-word-level}            \t output word-level SMV\n"
    " {y--verbosity} {u#}            \t verbosity level, from 0 (silent) to 10 (everything)\n"
    // clang-format on
    "\n");
}
