/*******************************************************************\

Module: Base for Verification Modules

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_EBMC_EBMC_BASE_H
#define CPROVER_EBMC_EBMC_BASE_H

#include <util/cmdline.h>
#include <util/message.h>
#include <util/std_expr.h>
#include <util/ui_message.h>

#include <solvers/sat/cnf.h>
#include <solvers/stack_decision_procedure.h>
#include <trans-netlist/bmc_map.h>
#include <trans-netlist/netlist.h>
#include <trans-netlist/trans_trace.h>

#include "ebmc_properties.h"
#include "transition_system.h"

#include <fstream>

class ebmc_baset
{
public:
  ebmc_baset(const cmdlinet &_cmdline,
             ui_message_handlert &_ui_message_handler);
  virtual ~ebmc_baset() { }

  int get_properties();
  void show_ldg(std::ostream &out);
  bool make_netlist(netlistt &);

  transition_systemt transition_system;

  using propertyt = ebmc_propertiest::propertyt;
  ebmc_propertiest properties;

protected:
  messaget message;
  const cmdlinet &cmdline;

  bool parse_property(const std::string &property);
  bool get_model_properties();

  bool parse();
  bool parse(const std::string &filename);
  bool typecheck();

  std::size_t bound;

public:
  int do_compute_ct();
};

#endif
