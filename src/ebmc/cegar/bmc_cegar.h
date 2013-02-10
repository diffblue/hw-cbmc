/*******************************************************************\

Module: CEGAR for BMC

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <std_expr.h>
#include <message.h>
#include <namespace.h>

#include <trans/bmc_map.h>
#include <trans/netlist.h>

class bmc_cegart
{
public:
  bmc_cegart(
    symbol_tablet &_symbol_table,
    const irep_idt &_main_module,
    messaget &_message,
    const std::list<exprt> &_properties,
    bool _verbose):
    symbol_table(_symbol_table),
    ns(_symbol_table),
    main_module(_main_module),
    message(_message),
    properties(_properties),
    verbose(_verbose)
  {
  }

  void bmc_cegar();
  
protected:
  symbol_tablet &symbol_table;
  const namespacet ns;
  const irep_idt &main_module;
  messaget &message;
  const std::list<exprt> &properties;
  
  bool verbose;
  
  bmc_mapt bmc_map;
  netlistt concrete_netlist, abstract_netlist;

  bool initial_abstraction;
  
  typedef std::set<literalt> cut_pointst;
  cut_pointst cut_points;
  
  void make_netlist();
  
  void cegar_loop();
  
  void abstract();
  void refine();
  bool verify(unsigned bound);
  bool simulate(unsigned bound);
  unsigned compute_ct();

  void unwind(
    unsigned bound,
    const netlistt &netlist,
    propt &prop);
  
  std::list<bvt> prop_bv;
};
