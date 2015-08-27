/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef EBMC_PARSEOPTIONS_H
#define EBMC_PARSEOPTIONS_H

#include <util/parse_options.h>

class ebmc_parse_optionst:public parse_options_baset
{
public:
  virtual int doit();
  virtual void help();

  ebmc_parse_optionst(int argc, const char **argv):
    parse_options_baset("(diameter)(ediameter)"
    "(diatest)(statebits):(bound):"
    "(show-parse)(show-varmap)(show-symbol-table)(show-netlist)"
    "(show-ldg)(show-modules)(show-trans)"
    "(dimacs)(module):(top):"
    "(verbosity):(gui)(po)(cegar)"
    "(k-induction)(2pi)(bound2):(outfile):(xml-ui)"
    "(show-properties)(property):p:"
    "(reset):"
    "(version)(verilog-rtl)(verilog-netlist)"
    "(compute-interpolant)(interpolation)(interpolation-vmcai)"
    "(interpolation-word)(interpolator):"
    "(smt1)(smt2)(boolector)(z3)(cvc4)(yices)(prover)(lifter)"
    "(aig)(stop-induction)(stop-minimize)(start):(coverage)(naive)"
    "(compute-ct)(dot-netlist)(smv-netlist)(vcd):I:",
    argc, argv)
  {
  }
   
  virtual ~ebmc_parse_optionst() { }
  
protected:
  void register_languages();
};

#endif
