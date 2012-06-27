#ifndef EBMC_COVERAGE_INTERPOLATION
#define EBMC_COVERAGE_INTERPOLATION

#include "../interpolation/interpolation_netlist.h"
#include "assumptions.h"

class interpolation_coveraget: public interpolationt_netlist, public assumptionst
{
private:
  const interpolationt_netlist & original_interpolator;
  interpolatort final_decision_interpolator;  
public:
   void check_invariant();
interpolation_coveraget(const cmdlinet &cmdline,
                        const netlistt &netlist1,
                        std::map<std::string, force_multiplexert> &force_selects_node1,
                        std::map<std::string, force_multiplexert> &force_selects_latch1,
                        const interpolationt_netlist & interpolator,
                        bool do_force1 = true):
  interpolationt_netlist(cmdline), assumptionst(force_selects_node1, force_selects_latch1), original_interpolator(interpolator)
    {
      working_netlist = netlist1;
      bound = original_interpolator.return_bound();
      do_force = do_force1;

    }
  interpolation_resolution_prooft &get_final_resolution_proof() 
  {
    return final_decision_interpolator.get_resolution_proof();
  }

  void do_coverage();
  virtual int do_interpolation();
protected:
  int induction_step();
  int do_interpolation(interpolatort *interpolator);
  
  bool do_force;
  unsigned fixed_bound;
  void remove_not_covered(std::map<std::string, force_multiplexert> &given_map);
  bool check_partition_one_implies_interpolant(const bit_interpolantt &current_inter);
  bool check_partition_two_and_interpolant(const bit_interpolantt &current_inter);
  
  int iteration()  ;
};

#endif
