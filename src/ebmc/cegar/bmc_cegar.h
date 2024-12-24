/*******************************************************************\

Module: CEGAR for BMC

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef EBMC_CEGAR_BMC_CEGAR_H
#define EBMC_CEGAR_BMC_CEGAR_H

#include <util/message.h>
#include <util/namespace.h>
#include <util/std_expr.h>

#include <ebmc/ebmc_properties.h>
#include <ebmc/transition_system.h>
#include <trans-netlist/bmc_map.h>
#include <trans-netlist/netlist.h>

class cnft;

class bmc_cegart:public messaget
{
public:
  bmc_cegart(
    const netlistt &_netlist,
    ebmc_propertiest &_properties,
    const namespacet &_ns,
    message_handlert &_message_handler)
    : messaget(_message_handler),
      properties(_properties),
      concrete_netlist(_netlist),
      ns(_ns)
  {
  }

  void bmc_cegar();
  
protected:
  ebmc_propertiest &properties;
  bmc_mapt bmc_map;
  netlistt concrete_netlist, abstract_netlist;
  const namespacet &ns;

  bool initial_abstraction;
  
  typedef std::set<literalt> cut_pointst;
  cut_pointst cut_points;

  void cegar_loop();
  
  void abstract();
  void refine();
  bool verify(std::size_t bound);
  bool simulate(std::size_t bound);
  std::size_t compute_ct();

  void unwind(std::size_t bound, const netlistt &netlist, cnft &solver);

  std::map<irep_idt, bvt> prop_bv_map;
};

class ebmc_propertiest;
class message_handlert;
class netlistt;

int do_bmc_cegar(
  const netlistt &,
  ebmc_propertiest &,
  const namespacet &,
  message_handlert &);

#endif // EBMC_CEGAR_BMC_CEGAR_H
