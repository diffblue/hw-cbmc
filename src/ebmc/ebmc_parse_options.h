/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef EBMC_PARSEOPTIONS_H
#define EBMC_PARSEOPTIONS_H

#include <util/parse_options.h>
#include <util/ui_message.h>

#include "ebmc_version.h"

class ebmc_parse_optionst:public parse_options_baset
{
public:
  virtual int doit();
  virtual void help();

  ebmc_parse_optionst(int argc, const char **argv)
    : parse_options_baset(
        "(diameter)(ediameter)"
        "(diatest)(statebits):(bound):(max-bound):"
        "(show-parse)(show-varmap)(show-symbol-table)(show-netlist)"
        "(show-ldg)(show-modules)(show-trans)(show-bdds)"
        "(show-properties)(property):p:(trace)"
        "(dimacs)(module):(top):"
        "(po)(cegar)(k-induction)(2pi)(bound2):"
        "(outfile):(xml-ui)(verbosity):(gui)"
        "(reset):"
        "(version)(verilog-rtl)(verilog-netlist)"
        "(compute-interpolant)(interpolation)(interpolation-vmcai)"
        "(ic3)(property):(constr)(h)(new-mode)(aiger)"
        "(interpolation-word)(interpolator):(bdd)"
        "(smt1)(smt2)(boolector)(z3)(cvc4)(yices)(mathsat)(prover)(lifter)"
        "(aig)(stop-induction)(stop-minimize)(start):(coverage)(naive)"
        "(compute-ct)(dot-netlist)(smv-netlist)(vcd):"
        "I:(preprocess)",
        argc,
        argv,
        std::string("EBMC ") + EBMC_VERSION),
      ui_message_handler(cmdline, "EBMC " EBMC_VERSION)
  {
  }

  virtual ~ebmc_parse_optionst() { }
  
protected:
  void register_languages();
  
  ui_message_handlert ui_message_handler;
};

#endif
