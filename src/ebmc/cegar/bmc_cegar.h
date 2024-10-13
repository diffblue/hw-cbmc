/*******************************************************************\

Module: CEGAR for BMC

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/message.h>
#include <util/namespace.h>
#include <util/std_expr.h>

#include <trans-netlist/bmc_map.h>
#include <trans-netlist/netlist.h>

#include "../ebmc_properties.h"
#include "../transition_system.h"

class bmc_cegart
{
public:
  bmc_cegart(
    transition_systemt &_transition_system,
    ebmc_propertiest &_properties,
    message_handlert &_message_handler)
    : symbol_table(_transition_system.symbol_table),
      ns(_transition_system.symbol_table),
      main_module(_transition_system.main_symbol->name),
      properties(_properties),
      message(_message_handler)
  {
  }

  void bmc_cegar();
  
protected:
  symbol_table_baset &symbol_table;
  const namespacet ns;
  const irep_idt &main_module;
  ebmc_propertiest &properties;
  messaget message;

  bmc_mapt bmc_map;
  netlistt concrete_netlist, abstract_netlist;

  bool initial_abstraction;
  
  typedef std::set<literalt> cut_pointst;
  cut_pointst cut_points;
  
  void make_netlist();
  
  void cegar_loop();
  
  void abstract();
  void refine();
  bool verify(std::size_t bound);
  bool simulate(std::size_t bound);
  std::size_t compute_ct();

  void unwind(std::size_t bound, const netlistt &netlist, propt &prop);
};
