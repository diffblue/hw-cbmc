/*******************************************************************\

Module: compute-interpolant

Author: Mitra

\*******************************************************************/

#include <fstream>

#include <solvers/sat/read_dimacs_cnf.h>
#include <solvers/sat/satcheck.h>
#include <solvers/sat/satcheck_minisat.h>
#include <solvers/prop/aig_formula.h>

#include <interpolation/bitlevel/aig_minimizer.h>
#ifdef HYPER
#include <interpolation/bitlevel/satcheck_bit_interpolation_hyper.h>
#include <interpolation/bitlevel/satcheck_minisat_hyper.h>
#else
#include <interpolation/bitlevel/satcheck_minisat_normal.h>
#include <interpolation/bitlevel/satcheck_bit_interpolation_normal.h>
#endif
#include <interpolation/bitlevel/strengthen_interpolant.h>

#include "compute-interpolant.h"

#if 0
static void reverse_partitions(
#ifdef HYPER
    satcheck_minisat_hyper_prooft& interpolator)
#else
  satcheck_minisat_normal_prooft& interpolator)
#endif
{
    //find out the bit-level interpolant
#ifdef HYPER
  satcheck_bit_interpolation_hypert do_bit_interpolation_1(interpolator.get_resolution_proof(), 1);
#else
  satcheck_bit_interpolation_normalt do_bit_interpolation_1(interpolator.get_resolution_proof(), 1);
#endif
  aig_formulat i_bit_1= do_bit_interpolation_1.get_interpolant();
  std::cout << "bit-level interpolant\n";
  std::cout << i_bit_1 << std::endl;

#ifdef HYPER
  satcheck_bit_interpolation_hypert do_bit_interpolation_2(interpolator.get_resolution_proof(), 1, false);
#else
  satcheck_bit_interpolation_normalt do_bit_interpolation_2(interpolator.get_resolution_proof(), 1, false);
#endif
  aig_formulat i_bit_2= do_bit_interpolation_2.get_interpolant();
  std::cout << "bit-level interpolant\n";
  std::cout << i_bit_2 << std::endl;

  satcheckt solver1;
    //  namespacet ns(symbol_table);
  i_bit_1.add_variables(solver1);
  i_bit_2.add_variables(solver1);

  literalt l1 = i_bit_1.convert(solver1);
  literalt l2 = i_bit_2.convert(solver1);
 
    //check if i_bit_1 -> !i_bit_2
    //check if i_bit_1 /\ i_bit_2 is UNSAT
  solver1.l_set_to(l1, true);
  solver1.l_set_to(l2, true);
  switch(solver1.prop_solve())
  {
    case propt::P_SATISFIABLE:
      std::cout << "SAT: I1 !-> !I2" << std::endl;
      break;
    case propt::P_UNSATISFIABLE:
      std::cout << "UNSAT: I1 -> !I2" << std::endl;
      break;
 
    default:
      throw "unexpected result from SAT-solver";
  }
 
  satcheckt solver2;
    //  namespacet ns(symbol_table);
  i_bit_1.add_variables(solver2);
  i_bit_2.add_variables(solver2);
 
  literalt l1_2 = i_bit_1.convert(solver2);
  literalt l2_2 = i_bit_2.convert(solver2);
 
    //check if !i_bit_2 -> i_bit_1
    //check if !i_bit_1 /\ !i_bit_2 is UNSAT
  solver2.l_set_to(l1_2, false);
  solver2.l_set_to(l2_2, false);
  switch(solver2.prop_solve())
  {
    case propt::P_SATISFIABLE:
      std::cout << "SAT: !I2 !-> I1" << std::endl;
      break;
    case propt::P_UNSATISFIABLE:
      std::cout << "UNSAT: !I2 -> I1" << std::endl;
      break;
 
    default:
      throw "unexpected result from SAT-solver";
  }
}
 
/*******************************************************************\

Function: compute_interpolant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int compute_interpolant(
  const cmdlinet &cmdline)
{
  typedef std::vector<std::string> str_vec;
  int i = 1;
  std::vector<std::string> args = cmdline.args;
#ifdef HYPER
  satcheck_minisat_hyper_prooft sat_interpolant;
#else
   satcheck_minisat_normal_prooft sat_interpolant;
#endif
  std::cout << "parsing arguments " << std::endl;
  for(str_vec::iterator itr_val = args.begin();
      itr_val!=args.end();
      itr_val++)
  {
    sat_interpolant.set_partition_id(i);
    std::string input = *itr_val;
    std::cout << "file name " << input << std::endl;
    std::ifstream cnf(input.c_str());
#ifdef VERBOSE
    unsigned orig_clauses = sat_interpolant.get_no_of_clauses();
    std::cout << "orig_clauses " << orig_clauses << std::endl;
#endif
    read_dimacs_cnf(cnf, sat_interpolant);
#ifdef VERBOSE
    std::cout << "clauses " <<  sat_interpolant.get_no_of_clauses() << std::endl;
#endif
    i++;
  }

  std::cout << "parsing arguments Done" << std::endl;

  std::cout << "Minisat Solver Running" << std::endl;
  sat_interpolant.prop_solve();
  std::cout << "Minisat Solver Done" << std::endl;

  std::cout << "Computing Interpolant" << std::endl;

#ifdef HYPER
  //compute interpolant from a hyper resolution step
  satcheck_bit_interpolation_hypert do_interpolation(sat_interpolant.get_resolution_proof(), 1);
#else
  satcheck_bit_interpolation_normalt do_interpolation(sat_interpolant.get_resolution_proof(), 1);
#endif
    aig_formulat interpolant = do_interpolation.get_interpolant();
  
  reverse_partitions(sat_interpolant);
  std::cout << "Computing Interpolant Done" << std::endl;
  return 0;
}

#endif
