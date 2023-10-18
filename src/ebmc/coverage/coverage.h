/*******************************************************************\

Module: Coverage Measurement

Author: Mitra Purandare

\*******************************************************************/

#ifndef EBMC_COVERAGE_H
#define EBMC_COVERAGE_H

#include <ebmc/ebmc_base.h>
#include <trans-netlist/netlist.h>

#include "assumptions.h"

class coveraget: public ebmc_baset
{
 private:
  netlistt original_netlist;
  netlistt working_netlist;
  
  std::map<std::string, force_multiplexert> force_selects_node;

  std::map<std::string, force_multiplexert> force_selects_latch;
  
  const cmdlinet &cmdline;
  
 public:
  int measure_coverage();

  coveraget(const cmdlinet &cmdline1)
    :ebmc_baset(cmdline1), cmdline(cmdline1)
  {}
private:
  void introduce_multiplexor_for_latch(var_mapt::vart &var, irep_idt t,
                                       unsigned i);
  void introduce_multiplexor(unsigned n);
  void make_new_netlist();
  unsigned make_new_var_node(const irep_idt &name);

  void check_original_core(const interpolation_resolution_prooft & proof,
                           const interpolationt_netlist & original_interpolator);
  void remove_notcovered(std::map< std::string, force_multiplexert> &given_map,
                         const std::vector<bool> &core,
                         const bmc_mapt &cm,
                         const interpolationt_netlist & original_interpolator);
  void print_result_per_latch();
  void print_total_stats();
  void check_peripherality(std::map< std::string, force_multiplexert> &given_selects_map,
                           const interpolation_resolution_prooft & proof);
  int measure_coverage_naive();
};

#endif // EBMC_COVERAGE_H
