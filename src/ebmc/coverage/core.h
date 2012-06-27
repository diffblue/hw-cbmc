#ifndef CPROVER_CORE_H
#define CPROVER_CORE_H

#include "interpolation/bitlevel/normal_resolution_proof.h"
#include "../interpolation/interpolation_netlist.h"
#include "assumptions.h"

class coret
{
public:
  
  const interpolation_resolution_prooft &original_proof;
  std::vector<bool> core;
  bool remove;
  
coret(const interpolation_resolution_prooft &proof):original_proof(proof)
  {
    remove = true;
  }
  
  
};


class check_coret: public coret
{
  unsigned bound;
  const netlistt &working_netlist;
  std::map<std::string, force_multiplexert> &force_selects_node;
  std::map<std::string, force_multiplexert> &force_selects_latch;
  
  void remove_notcovered(std::map< std::string, force_multiplexert> &given_map,
                         const bmc_mapt &check_map);

public:
  
  void check_original_core();
check_coret(const interpolation_resolution_prooft &proof,
            unsigned bound, netlistt &wn,
            std::map<std::string, force_multiplexert> &f_node,
            std::map<std::string, force_multiplexert> &f_latch)
  :coret(proof),
    bound(bound), working_netlist(wn), force_selects_node(f_node), force_selects_latch(f_latch)
  {}
};


#endif
