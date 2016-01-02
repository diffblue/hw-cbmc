/*******************************************************************\

Module: Base for Verification Modules

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_EBMC_EBMC_BASE_H
#define CPROVER_EBMC_EBMC_BASE_H

#include <util/ui_message.h>
#include <util/std_expr.h>

#include <langapi/language_ui.h>
#include <trans-netlist/netlist.h>
#include <trans-netlist/trans_trace.h>
#include <trans-netlist/bmc_map.h>
#include <solvers/prop/prop_conv.h>
#include <solvers/sat/cnf.h>

class ebmc_baset:public language_uit
{
public:
  ebmc_baset(const cmdlinet &_cmdline);
  virtual ~ebmc_baset() { }

  int get_model();

protected:
  const cmdlinet &cmdline;

  const symbolt *main_symbol;
  transt trans_expr; // transition system expression
  
  bool get_main();
  bool get_bound();
    
  int finish(prop_convt &solver);
  int finish(const bmc_mapt &bmc_map, propt &solver);

  void show_trace(const trans_tracet &trans_trace);
  
  void check_property(prop_convt &solver, bool convert_only);
  void check_property(bmc_mapt &bmc_map, cnft &solver, bool convert_only);

  // word-level
  int do_ebmc(prop_convt &solver, bool convert_only);

  // bit-level
  int do_ebmc(cnft &solver, bool convert_only);
  
  bool parse_property(const std::string &property);
  bool get_model_properties();
  void show_properties();

  void unwind(decision_proceduret &solver);
  void unwind(decision_proceduret &solver, unsigned _bound, bool initial_state);
  
  unsigned bound;

  struct propertyt
  {
  public:
    irep_idt name;
    source_locationt location;
    std::string expr_string;
    irep_idt mode;
    exprt expr;
    std::string description;
    enum class statust { DISABLED, SUCCESS, FAILURE, UNKNOWN } status;
    
    propertyt():status(statust::UNKNOWN)
    {
    }
    
    trans_tracet counterexample;
  };

  typedef std::list<propertyt> propertiest;
  propertiest properties;
  
  typedef std::list<exprt> prop_expr_listt;
  prop_expr_listt prop_expr_list;

  typedef std::list<std::string> prop_name_listt;
  prop_name_listt prop_name_list;

  // the truth value of the properties in the time frames  
  std::list<bvt> prop_bv;
  
  void report_failure();
  void report_success();
  void report_results();
  
  void show_ldg(std::ostream &out);
  bool make_netlist(netlistt &netlist);  

public:  
  // solvers
  int do_compute_ct();
  int do_dimacs();
  int do_cvc4();
  int do_smt1();
  int do_smt2();
  int do_boolector();
  int do_mathsat();
  int do_yices();
  int do_z3();
  int do_sat();
  int do_prover();
  int do_lifter();
};

#endif
