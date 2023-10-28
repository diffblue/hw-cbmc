/*******************************************************************\

Module: EBMC's Solvers

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/cmdline.h>
#include <util/unicode.h>

#include <solvers/flattening/boolbv.h>
#include <solvers/sat/dimacs_cnf.h>
#include <solvers/sat/satcheck.h>
#include <solvers/smt2/smt2_dec.h>

#include <fstream>
#include <iostream>

#ifdef HAVE_PROVER
#include <prover/prover_sat.h>
#include <prover/lifter.h>
#endif

#include "dimacs_writer.h"
#include "ebmc_base.h"
#include "ebmc_solver_factory.h"
#include "ebmc_version.h"
#include "show_formula_solver.h"

/*******************************************************************\

Function: ebmc_baset::do_bit_level_bmc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int ebmc_baset::do_bit_level_bmc()
{
  if(cmdline.isset("outfile"))
  {
    const std::string filename=cmdline.get_value("outfile");
    std::ofstream out(widen_if_needed(filename));

    if(!out)
    {
      message.error() << "Failed to open `" << filename << "'" << messaget::eom;
      return 1;
    }

    dimacs_cnf_writert dimacs_cnf_writer{out, message.get_message_handler()};

    return do_bit_level_bmc(dimacs_cnf_writer, true);
  }
  else
  {
    satcheckt satcheck{message.get_message_handler()};

    message.status() << "Using " << satcheck.solver_text() << messaget::eom;

    return do_bit_level_bmc(satcheck, false);
  }
}
