/*******************************************************************\

Module: Word Interpolation

Author: Mitra Purandare

\*******************************************************************/

#ifndef CPROVER_EBMC_INTERPOLATION_WORD_H
#define CPROVER_EBMC_INTERPOLATION_WORD_H

#include <cmdline.h>
#include <fstream>
#include <sstream>
#include <namespace.h>

#include <i2string.h>
#include <expr_util.h>
#include <find_symbols.h>
#include <time_stopping.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/boolbv.h>
#include <trans/instantiate.h>
#include <trans/property.h>
#include <trans/trans_trace.h>
#include <ebmc/ebmc_base.h>

#include <interpolation/wordlevel/skeleton_map.h>
#include <interpolation/wordlevel/satcheck_word_interpolation_normal.h>
#include <interpolation/wordlevel/mixed_interpolant.h>
//#include <interpolation/bitlevel/bv_expr.h>
#include <interpolation/bitlevel/strengthen_interpolant.h>
#include <interpolation/bitlevel/aig_minimizer.h>
#include <interpolation/bitlevel/satcheck_minisat_normal.h>

int do_interpolation_word(
  const cmdlinet &cmdline);

/*******************************************************************\

   Class: interpolationt

 Purpose:

\*******************************************************************/

class interpolationt_word:public ebmc_baset
{
public:
interpolationt_word(
  const cmdlinet &cmdline)
  :ebmc_baset(cmdline)
  {
  }

  int do_interpolation();

protected:
  int check_initial_state();
  int iteration();

  void build_partition1(
    prop_convt &solver);
  void build_partition2(
    prop_convt &solver);
  void build_property(
    prop_convt &solver);
  
  typedef satcheck_minisat_normal_prooft interpolatort;
  typedef satcheck_word_interpolation_normalt do_interpolationt;

  void get_interpolant(
    boolbvt &solver,
    interpolatort& interpolator);

  bool reached_fixedpoint();

  unsigned iteration_number;

    //  std::vector<bit_interpolantt> interpolants; //bit-level interpolants
  std::vector<exprt> interpolants; //bit-level interpolants  
    // map from variables of timeframe #1 to timeframe #0
  typedef std::map<unsigned, unsigned> variable_mapt;
  variable_mapt variable_map;

  std::vector<class bv_exprt> reverse_map;
  
//  std::map<unsigned, std::pair<exprt, unsigned> > map_expr;

  void map_variables(
    bit_interpolantt &f);

  void map_literal(
    aig_nodet &l);

  void map_to_timeframe_zero(exprt &t1);
  
  typedef std::map<unsigned, std::string> variable_namest;
  variable_namest variable_names;
  
  void build_variable_map(
    boolbvt &boolbv);
  int induction_step();

  fine_timet sat_time;

  std::set<skeleton_mapt> skeleton_vars;
    //some checks
  void reverse_partitions(
    boolbvt& solver,
    interpolatort &interpolator);

  literalt start_instantiate_convert(
    prop_convt &prop_conv,
    const exprt &t1,
    const namespacet &ns);

  void instantiate_with_if_lifting(prop_convt &solver,
                                   const exprt &expr,
                                   unsigned tf);
  
  literalt instantiate_convert_with_if_lifting(prop_convt &solver,
                                               const exprt &expr,
                                               unsigned tf);
  bool check_partition_one_implies_interpolant(
    const exprt &t);
  
  bool check_partition_two_and_interpolant(
    const exprt &t);
  
  literalt convert_as_it_is(
    prop_convt &prop_conv,
    const exprt &t1);
};

#endif
