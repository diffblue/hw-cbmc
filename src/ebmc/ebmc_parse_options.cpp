/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include "version.h"
#include "show_trans.h"
#include "k_induction.h"
#include "ebmc_base.h"
#include "ebmc_parse_options.h"

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
  register_languages();

  if(cmdline.isset("version"))
  {
    std::cout << EBMC_VERSION << '\n';
    return 0;
  }

  #if 0
  if(cmdline.isset("diatest"))
  {
    if(get_bound()) return 1;

    if(!cmdline.isset("statebits"))
    {
      error("error: must provide number of state bits");
      help();
      return 1;
    }

    diatest(bound, atoi(cmdline.getval("statebits")));

    return 0;
  }
  #endif
  
  if(cmdline.isset("cegar"))
  {
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
    #endif
    return 0;
  }

  if(cmdline.isset("coverage"))
  {
#ifdef HAVE_INTERPOLATION
    std::cout << "found coverage\n";
//    return do_coverage(cmdline);
//    if(do_coverage)
//    {
      coveraget coverage(cmdline);
      return coverage.measure_coverage();
//    }
#endif
  }
  
  
  if(cmdline.isset("k-induction"))
    return do_k_induction(cmdline);

 if(cmdline.isset("interpolation-word"))
  {
  std::cout << "This option is currently disabled\n";
  return 1;
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
std::cout << "This option is currently disabled\n";
  return 1;

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
    language_uit language_ui("EBMC " EBMC_VERSION, cmdline);
    language_ui.error() << "No support for interpolation linked in" << messaget::eom;
    return 1; 
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
    return show_trans(cmdline);

  if(cmdline.isset("verilog-rtl"))
    return show_trans_verilog_rtl(cmdline);

  if(cmdline.isset("verilog-netlist"))
    return show_trans_verilog_netlist(cmdline);

  {
    ebmc_baset ebmc_base(cmdline);
  
    int result=ebmc_base.get_model();
    if(result!=-1) return result;

    if(cmdline.isset("dimacs"))
      return ebmc_base.do_dimacs();
    else if(cmdline.isset("cvc4"))
      return ebmc_base.do_cvc4();
    else if(cmdline.isset("boolector"))
      return ebmc_base.do_boolector();
    else if(cmdline.isset("z3"))
      return ebmc_base.do_z3();
    else if(cmdline.isset("yices"))
      return ebmc_base.do_yices();
    else if(cmdline.isset("smt1"))
      return ebmc_base.do_smt1();
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
    "* *      EBMC - Copyright (C) 2001-2015 Daniel Kroening     * *\n"
    "* *                     Version " EBMC_VERSION "                         * *\n"
    "* *     University of Oxford, Computer Science Department   * *\n"
    "* *                  kroening@kroening.com                  * *\n"
    "\n"
    "Usage:                             Purpose:\n"
    "\n"
    " ebmc [-?] [-h] [--help]           show help\n"
    " ebmc file ...                     source file names\n"
    "\n"
    "Additonal options:\n"
    " --bound <nr>                      set bound (default: 1)\n"
    " --module <module>                 set top module (deprecated)\n"
    " --top <module>                    set top module\n"
    " -p <expr>                         specify a property\n"
    " --outfile <name>                  set output file name (default: stdout)\n"
    " --vcd <vcd filename>              generate traces in VCD format\n"
    " --show-properties                 list the properties in the model\n"
    " --property <id>                   check the property with given ID\n"
    " -I path                           set include path\n"
    " --reset <expr>                    set up module reset\n"
    "\n"
    "Methods:\n"
    " --k-induction                     do k-induction with k=bound\n"
    //" --interpolation                   use bit-level interpolants\n"
    //" --interpolation-word              use word-level interpolants\n"
    //" --diameter                        perform recurrence diameter test\n"
    "\n"
    "Solvers:\n"
    " --aig                             bit-level SAT with AIGs\n"
    " --dimacs                          output bit-level CNF in DIMACS format\n"
    " --smt1                            output word-level SMT 1 formula\n"
    " --smt2                            output word-level SMT 2 formula\n"
    " --boolector                       use Boolector as solver\n"
    " --cvc4                            use CVC4 as solver\n"
    " --yices                           use Yices as solver\n"
    " --z3                              use Z3 as solver\n"
    "\n"
    "Debugging options:\n"
    " --show-parse                      show parse trees\n"
    " --show-varmap                     show variable map\n"
    " --show-netlist                    show netlist\n"
    " --show-ldg                        show latch dependencies\n"
    " --smv-netlist                     show netlist in SMV format\n"
    " --dot-netlist                     show netlist in DOT format\n"
    " --show-trans                      show transition system\n"
    "\n";
}
