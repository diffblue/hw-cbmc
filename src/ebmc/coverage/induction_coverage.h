#ifndef EBMC_COVERAGE_INDUCTION
#define EBMC_COVERAGE_INDUCTION

#include "../interpolation/interpolation_netlist.h"
#include "assumptions.h"

enum induction_resultt {INDUCTIVE, NOTINDUCTIVE, REALCE};  

class induction_coveraget: public ebmc_baset, public assumptionst
{
private:
  netlistt netlist;
  const interpolationt_netlist & original_interpolator;
  
public:
  prop_expr_listt prop_expr_list1;

induction_coveraget(const cmdlinet &cmdline,
                    const netlistt &netlist1,
                    std::map<std::string, force_multiplexert> &force_selects_node1,
                    std::map<std::string, force_multiplexert> &force_selects_latch1,
                    interpolationt_netlist & original_interpolator1):
  ebmc_baset(cmdline), assumptionst(force_selects_node1, force_selects_latch1), original_interpolator(original_interpolator1)
    {
      netlist = netlist1;
    }
  
  
    
  void do_coverage();
  
protected:

  literalt unwind(cnft &solver, const bmc_mapt &bmc_map,
                  unsigned t, bool initial_states,
                  bool transition);
  void remove_not_covered_from_scratch(const bmc_mapt &bmc_map,
                          std::map< std::string, force_multiplexert> &given_map,
                          satcheckt &solver);
  
  void remove_not_covered_test_from_scratch(const bmc_mapt &bmc_map,
                                            std::map< std::string, force_multiplexert> &given_map2);
  void remove_covered(const bmc_mapt &bmc_map,
                                   std::map< std::string, force_multiplexert> &given_selects_map,
                                   satcheckt &solver,
                                   std::list<bvt> &prop_bv1,
                                   unsigned bound);

  void remove_not_covered(const bmc_mapt &bmc_map,
                          std::map< std::string, force_multiplexert> &given_map,
                          satcheck_minisat_normal_prooft &solver);

  void check_invariant();
  void check_ce(unsigned bound);

  void add_clause(const interpolation_resolution_prooft & proof,
                  satcheckt &new_solver,
                  std::map< std::string, force_multiplexert> &given_selects_map,
                  const bmc_mapt &bmc_map);

  induction_resultt is_inductive(bool force,
                                   satcheckt &interpolator,
                                   bool assume=true);

    induction_resultt is_inductive1(bool force,
                                   satcheck_minisat_normal_prooft &interpolator);

//  void check_peripherality(std::map< std::string, force_multiplexert> &given_selects_map,
//                                              const bmc_mapt &bmc_map,
//                                              const interpolation_resolution_prooft & proof);
  
  
};

#endif
