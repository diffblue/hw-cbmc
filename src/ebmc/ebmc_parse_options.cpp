/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ebmc_parse_options.h"

#include <util/config.h>
#include <util/exit_codes.h>
#include <util/help_formatter.h>
#include <util/string2int.h>

#include "bdd_engine.h"
#include "diatest.h"
#include "ebmc_base.h"
#include "ebmc_error.h"
#include "ebmc_version.h"
#include "ic3_engine.h"
#include "k_induction.h"
#include "random_traces.h"
#include "ranking_function.h"
#include "show_trans.h"

#include <iostream>

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
  if(config.set(cmdline))
  {
    usage_error();
    return CPROVER_EXIT_USAGE_ERROR;
  }

  register_languages();

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

    if(cmdline.isset("cegar"))
    {
      throw ebmc_errort() << "This option is currently disabled";

#if 0
      namespacet ns(symbol_table);
      var_mapt var_map(symbol_table, main_symbol->name);

      bmc_cegart bmc_cegar(
        var_map,
        *trans_expr,
        ns,
        *this,
        prop_expr_list);

      bmc_cegar.bmc_cegar();
      return 0;
#endif
    }

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

    if(cmdline.isset("ic3"))
      return do_ic3(cmdline, ui_message_handler);

    if(cmdline.isset("k-induction"))
      return do_k_induction(cmdline, ui_message_handler);

    if(cmdline.isset("ranking-function"))
      return do_ranking_function(cmdline, ui_message_handler);

    if(cmdline.isset("bdd") || cmdline.isset("show-bdds"))
      return do_bdd(cmdline, ui_message_handler);

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

    if(cmdline.isset("show-trans"))
      return show_trans(cmdline, ui_message_handler);

    if(cmdline.isset("verilog-rtl"))
      return show_trans_verilog_rtl(cmdline, ui_message_handler);

    if(cmdline.isset("verilog-netlist"))
      return show_trans_verilog_netlist(cmdline, ui_message_handler);

    {
      ebmc_baset ebmc_base(cmdline, ui_message_handler);

      int result = ebmc_base.get_transition_system();

      if(result != -1)
        return result;

      result = ebmc_base.get_properties();

      if(result != -1)
        return result;

      if(cmdline.isset("dimacs"))
        return ebmc_base.do_dimacs();
      else if(cmdline.isset("cvc4"))
        return ebmc_base.do_cvc4();
      else if(cmdline.isset("boolector"))
        return ebmc_base.do_boolector();
      else if(cmdline.isset("z3"))
        return ebmc_base.do_z3();
      else if(cmdline.isset("mathsat"))
        return ebmc_base.do_mathsat();
      else if(cmdline.isset("yices"))
        return ebmc_base.do_yices();
      else if(cmdline.isset("show-formula"))
        return ebmc_base.do_show_formula();
      else if(cmdline.isset("smt2"))
        return ebmc_base.do_smt2();
      else if(cmdline.isset("prover"))
        return ebmc_base.do_prover();
      else if(cmdline.isset("lifter"))
        return ebmc_base.do_lifter();
      else if(cmdline.isset("compute-ct"))
        return ebmc_base.do_compute_ct();
      else
        return ebmc_base.do_sat();
    }
  }
  catch(const ebmc_errort &ebmc_error)
  {
    if(!ebmc_error.what().empty())
    {
      messaget message(ui_message_handler);
      message.error() << "error: " << messaget::red << ebmc_error.what()
                      << messaget::reset << messaget::eom;
    }
    return CPROVER_EXIT_EXCEPTION;
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
  std::cout <<
    "\n"
    "* *      EBMC - Copyright (C) 2001-2017 Daniel Kroening     * *\n"
    "* *                     Version " EBMC_VERSION "                         * *\n"
    "* *     University of Oxford, Computer Science Department   * *\n"
    "* *                  kroening@kroening.com                  * *\n"
    "\n";

  std::cout << help_formatter(
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
    " {y--show-properties}           \t list the properties in the model\n"
    " {y--property} {uid}            \t check the property with given ID\n"
    " {y-I} {upath}                  \t set include path\n"
    " {y--reset} {uexpr}             \t set up module reset\n"
    "\n"
    "Methods:\n"
    " {y--k-induction}               \t do k-induction with k=bound\n"
    " {y--bdd}                       \t use (unbounded) BDD engine\n"
    " {y--ic3}                       \t use IC3 engine with options described below\n"
    "    {y--constr}                 \t use constraints specified in 'file.cnstr'\n"
    "    {y--new-mode}               \t new mode is switched on\n"
    "    {y--aiger}                  \t print out the instance in aiger format\n"
    " {y--random-traces} {unumber}   \t generate the given number of random traces\n"
    "       {y--random-seed} {unumber}\t use the given random seed\n"
    " {y--ranking-function} {uf}     \t prove a liveness property using given ranking funnction (experimental)\n"
    "    {y--property} {uid}         \t the liveness property to prove\n"

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
    "Debugging options:\n"
    " {y--preprocess}                \t output the preprocessed source file\n"
    " {y--show-parse}                \t show parse trees\n"
    " {y--show-varmap}               \t show variable map\n"
    " {y--show-netlist}              \t show netlist\n"
    " {y--show-ldg}                  \t show latch dependencies\n"
    " {y--show-formula}              \t show the formula that is generated\n"
    " {y--smv-netlist}               \t show netlist in SMV format\n"
    " {y--dot-netlist}               \t show netlist in DOT format\n"
    " {y--show-trans}                \t show transition system\n"
    "\n");
}
