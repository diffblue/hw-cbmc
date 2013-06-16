/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef EBMC_PARSEOPTIONS_H
#define EBMC_PARSEOPTIONS_H

#include <util/parseoptions.h>

class ebmc_parseoptionst:public parseoptions_baset
{
public:
  virtual int doit();
  virtual void help();

  ebmc_parseoptionst(int argc, const char **argv):
    parseoptions_baset("(diameter)(ediameter)"
    "(diatest)(statebits):(bound):(show-parse)"
    "(show-varmap)(dimacs)(module):(show-netlist)"
    "(verbose)(gui)(po)(cegar)(property):(show-ldg)"
    "(k-induction)(2pi)(bound2):(outfile):(cvc)(xml-ui)"
    "(dplib)(show-modules)(show-claims)(claim):(lifter)"
    "(prover)(version)(verilog-rtl)(verilog-netlist)"
    "(compute-interpolant)(interpolation)(interpolation-vmcai)"
    "(interpolation-word)(interpolator):"
    "(smt1)(smt2)(boolector)(z3)(cvc3)(yices)"
    "(no-netlist)(stop-induction)(stop-minimize)(start):(coverage)(naive)"
    "(compute-ct)(dot-netlist)(smv-netlist)(vcd):I:",
    argc, argv)
  {
  }
   
  virtual ~ebmc_parseoptionst() { }
  
protected:
  void register_languages();
};

#endif
