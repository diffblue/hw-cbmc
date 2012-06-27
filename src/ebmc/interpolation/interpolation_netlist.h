/*******************************************************************\

   Class: interpolationt_netlist

 Purpose: performs model checking on netlists 
          using interpolants as over-approximations

\*******************************************************************/

#ifndef CPROVER_EBMC_INTERPOLATION_NETLIST_H
#define CPROVER_EBMC_INTERPOLATION_NETLIST_H

#include <cmdline.h>
#include <time_stopping.h>

#include <i2string.h>

#include <expr_util.h>
#include <find_symbols.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/boolbv.h>
#include <interpolation/bitlevel/bit_interpolant.h>
#include <trans/instantiate.h>
#include <trans/property.h>
#include <trans/counterexample.h>
#include <trans/netlist_trans.h>
#include <trans/unwind_netlist.h>
#include <trans/map_aigs.h>
#include <ebmc/ebmc_base.h>

#include <interpolation/bitlevel/aig_minimizer.h>
#ifdef HYPER
#include <interpolation/bitlevel/satcheck_bit_interpolation_hyper.h>
#include <interpolation/bitlevel/satcheck_minisat_hyper.h>
#else
#include <interpolation/bitlevel/satcheck_bit_interpolation_normal.h>
#include <interpolation/bitlevel/satcheck_minisat_normal.h>
#endif

enum unrolling_typet { KEN, JAO};

class interpolationt_netlist:public ebmc_baset
{
public:
    virtual void check_invariant();
interpolationt_netlist(
  const cmdlinet &cmdline)
  :ebmc_baset(cmdline), cmdline(cmdline)
  {
   fix_check_time = current_time() -current_time();
   minimization_time = 0;
   unrolling_type = KEN; //cumulative. only the interpolant in the last iteration is used in unwinding as per Jao.
     //Otherwise, 1 = Ken's style of unrolling
   do_coverage = false;
   minimize_interpolant = cmdline.isset("stop-minimize") ? false : true;
   do_induction = cmdline.isset("stop-induction") ? false : true;
  }

  virtual int do_interpolation();
  virtual int do_iteration();
  void set_unrolling_type(unrolling_typet t) {unrolling_type = t;}
  void set_netlist(netlistt t) {working_netlist = t;}
  void set_bound(unsigned t){bound = t;}
  void set_coverage(bool t) { do_coverage = t;}
  const netlistt & get_netlist() const
  {
    return working_netlist;
  }
  unsigned return_bound() const
  {
    return bound;
  }
  void set_minimize (bool t) 
  {
    minimize_interpolant = t;
  }
  void set_induction(bool t)
  {
    do_induction = t;
  }

  unsigned get_size_of_interpolants() const
  {
    return forward_interpolants.size();
  }

  const bit_interpolantt & get_interpolant(unsigned i) const
  {
    return forward_interpolants.at(i);
  }
  
#ifdef HYPER
  typedef satcheck_minisat_hyper_prooft interpolatort;
  typedef satcheck_bit_interpolation_hypert do_interpolationt;
#else
  typedef satcheck_minisat_normal_prooft interpolatort;
  typedef satcheck_bit_interpolation_normalt do_interpolationt;
#endif
  
protected:
  virtual int check_initial_state();
  virtual int iteration();
     

  typedef aig_sat_sweept minimizert;

  void build_partition1(
    interpolatort &interp,
    bmc_mapt &nbm);
  
  void build_partition2(
    interpolatort &interp,
    bmc_mapt &nbm);
  
  void build_property(
    interpolatort &interp,
    bmc_mapt &nbm);

  virtual void get_interpolant(
    interpolatort &interpolator,
    bmc_mapt &nbm);

#if 0
#ifndef HYPER
  virtual void get_strengthened_interpolant(
    interpolatort &interpolator);
#endif
#endif
  virtual bool reached_fixedpoint();
  virtual int induction_step();
  
  unsigned iteration_number;

  std::vector<bit_interpolantt> forward_interpolants;

  netlistt working_netlist;
//  bmc_mapt netlist_bmc_map;
  std::vector<bmc_mapt > last_aig_bmc_map;
    
  fine_timet sat_time;
  fine_timet fix_check_time;
  fine_timet minimization_time;
  unrolling_typet unrolling_type;
  bool do_coverage;
  bool minimize_interpolant;
  bool do_induction;

  const cmdlinet &cmdline;

  virtual bool check_partition_two_and_interpolant(const bit_interpolantt &current_inter);
  virtual bool check_partition_one_implies_interpolant(const bit_interpolantt &current_inter);
};

int do_interpolation_netlist(
  const cmdlinet &cmdline);

/*int do_coverage(
  const cmdlinet &cmdline);
*/
#endif
