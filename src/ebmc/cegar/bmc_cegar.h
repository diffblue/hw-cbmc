/*******************************************************************\

Module: CEGAR for BMC

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>
#include <util/message.h>
#include <util/namespace.h>

#include <trans-netlist/bmc_map.h>
#include <trans-netlist/netlist.h>

class bmc_cegart
{
public:
  bmc_cegart(
    symbol_table_baset &_symbol_table,
    const irep_idt &_main_module,
    message_handlert &_message_handler,
    const std::list<exprt> &_properties)
    : symbol_table(_symbol_table),
      ns(_symbol_table),
      main_module(_main_module),
      message(_message_handler),
      properties(_properties)
  {
  }

  void bmc_cegar();
  
protected:
  symbol_table_baset &symbol_table;
  const namespacet ns;
  const irep_idt &main_module;
  messaget message;
  const std::list<exprt> &properties;
  
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

  std::list<bvt> prop_bv;
};
