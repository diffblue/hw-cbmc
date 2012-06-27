/*******************************************************************\

Module: Interpolation

Author: Mitra Purandare

\*******************************************************************/

#ifndef CPROVER_EBMC_INTERPOLATION_H
#define CPROVER_EBMC_INTERPOLATION_H

#include <cmdline.h>
#include <iostream>
#include <fstream>
#include <sstream>

#include <i2string.h>
#include <expr_util.h>
#include <find_symbols.h>

#include <solvers/sat/satcheck.h>
#include <interpolation/bitlevel/bit_interpolant.h>
#include <solvers/flattening/boolbv.h>

#include <trans/instantiate.h>
#include <trans/property.h>
#include <trans/trans_trace.h>
#include <time_stopping.h>
#include <ebmc/ebmc_base.h>

#ifdef HYPER
#include <interpolation/bitlevel/satcheck_bit_interpolation_hyper.h>
#include <interpolation/bitlevel/satcheck_minisat_hyper.h>
#else
#include <interpolation/bitlevel/satcheck_bit_interpolation_normal.h>
#include <interpolation/bitlevel/satcheck_minisat_normal.h>
#endif

#include <interpolation/bitlevel/aig_minimizer.h>

int do_interpolation(const cmdlinet &cmdline);

/*******************************************************************\

   Class: interpolationt

 Purpose:

\*******************************************************************/

class interpolationt:public ebmc_baset
{
public:
interpolationt(
  const cmdlinet &cmdline)
  :ebmc_baset(cmdline)
  {
  }

  int do_interpolation();

protected:
  int check_initial_state();
  virtual int iteration();

  void build_partition1(
    prop_convt &solver);
  void build_partition2(
    prop_convt &solver);
  void build_property(
    prop_convt &solver);
#ifdef HYPER
  typedef satcheck_minisat_hyper_prooft interpolatort;
  typedef satcheck_bit_interpolation_hypert do_interpolationt;
#else
  typedef satcheck_minisat_normal_prooft interpolatort;
  typedef satcheck_bit_interpolation_normalt do_interpolationt;
#endif

  typedef aig_sat_sweept minimizert;

  void get_interpolant(
    interpolatort &interpolator);

  bool reached_fixedpoint();

  unsigned iteration_number;
    // reachable states: initial state plus this
  std::vector<class bit_interpolantt> interpolants;
  
    // map from variables of timeframe #1 to timeframe #0
  typedef std::map<unsigned, unsigned> variable_mapt;
  variable_mapt variable_map;

  void map_variables(
    class bit_interpolantt &f);
  void map_literal(
    aig_nodet &l);
  
  typedef std::map<unsigned, std::string> variable_namest;
  variable_namest variable_names;
  
  void build_variable_map(
    boolbvt &boolbv);
  bool check_partition_one_implies_interpolant();
  bool check_partition_two_and_interpolant();
  int induction_step();

  fine_timet sat_time;
};

#endif
