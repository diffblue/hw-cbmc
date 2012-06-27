/*******************************************************************\

   Class: interpolationt_netlist

   Purpose:

\*******************************************************************/

#ifndef CPROVER_EBMC_INTERPOLATION_NETLIST_VMCAI_H
#define CPROVER_EBMC_INTERPOLATION_NETLIST_VMCAI_H

//#include <propsolve/aig_prop.h>
#include "interpolation_netlist.h"
#if 0
int do_interpolation_netlist_vmcai(const cmdlinet &cmdline);

class interpolationt_netlist_vmcai:public interpolationt_netlist
{
public:

interpolationt_netlist_vmcai(
  const cmdlinet &cmdline)
  :interpolationt_netlist(cmdline){ }

  int do_forward_backward_reachability();

protected:
  unsigned iterations;
  unsigned backward_iteration_number, forward_iteration_number;
  bool forward_refinement, backward_refinement, forward_fixed_point, backward_fixed_point;
    // reachable states: initial state plus this
  std::vector<aig_formulat> backward_interpolants;
  std::vector<aig_formulat> approx_forward_reach_states;
  std::vector<aig_formulat> approx_backward_reach_states;
  std::vector<unsigned > forward_fault_locations; //contains possible corrections in order to generate UNSAT for forward UBMC
  std::vector<unsigned > backward_fault_locations; //contains possible corrections in order to generate UNSAT for backward UBMC

  void build_forward_partition1(
    interpolatort &interp);
  void build_forward_partition2(
    interpolatort &interp);
  void build_forward_property(
    interpolatort &interp);
  void get_interpolant(
    interpolatort &interpolator,
    bool forward);
  bool reached_fixedpoint(
    bool forward);

  int reachable_check();
  int check_forward_reachable_states();
  int check_backward_reachable_states();
  int forward_iteration();
  int backward_iteration();
  bool is_property();
  int Refine_Interpolant(
    boolbvt &solver,
    interpolatort& interpolator,
    bool forward);

  literalt union_previous_interpolants(
    bmc_mapt &bmc_map_inter,
    satcheckt &solver,
    bool forward);
  literalt intersect_approx_reachable_states(
    bmc_mapt &bmc_map_inter,
    satcheckt &solver,
    bool forward);

  void build_backward_partition1(
    interpolatort &interp);
  void build_backward_partition2(
    interpolatort &interp);
  void build_backward_property(
    interpolatort &interp);
  void check_if_interpolant_reach_intersect(
    bool forward);
};
#endif
#endif
