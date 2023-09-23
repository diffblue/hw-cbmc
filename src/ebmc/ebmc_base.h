/*******************************************************************\

Module: Base for Verification Modules

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_EBMC_EBMC_BASE_H
#define CPROVER_EBMC_EBMC_BASE_H

#include <fstream>

#include <langapi/language_file.h>
#include <solvers/prop/prop_conv_solver.h>
#include <solvers/sat/cnf.h>
#include <trans-netlist/bmc_map.h>
#include <trans-netlist/netlist.h>
#include <trans-netlist/trans_trace.h>

#include <util/cmdline.h>
#include <util/mathematical_expr.h>
#include <util/message.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/ui_message.h>

class ebmc_baset : public messaget {
public:
  ebmc_baset(const cmdlinet &_cmdline,
             ui_message_handlert &_ui_message_handler);
  virtual ~ebmc_baset() { }

  int get_model();

protected:
  symbol_tablet symbol_table;
  const cmdlinet &cmdline;
  language_filest language_files;

  const symbolt *main_symbol;
  optionalt<transt> trans_expr; // transition system expression

  int preprocess();

  bool get_main();
  bool get_bound();

  // word-level
  int do_bmc(prop_conv_solvert &solver, bool convert_only);
  int finish_bmc(prop_conv_solvert &solver);

  // bit-level
  int do_bmc(cnft &solver, bool convert_only);
  int finish_bmc(const bmc_mapt &bmc_map, propt &solver);
  
  bool parse_property(const std::string &property);
  bool get_model_properties();
  void show_properties();

  bool parse();
  bool parse(const std::string &filename);
  bool typecheck();

  unsigned bound;

  struct propertyt
  {
  public:
    unsigned number;
    irep_idt name;
    source_locationt location;
    std::string expr_string;
    irep_idt mode;
    exprt expr;
    bvt timeframe_literals;
    std::string description;
    enum class statust { DISABLED, SUCCESS, FAILURE, UNKNOWN } status;
    
    inline bool is_disabled() const
    {
      return status==statust::DISABLED;
    }
    
    inline bool is_failure() const
    {
      return status==statust::FAILURE;
    }
    
    inline void disable()
    {
      status=statust::DISABLED;
    }
    
    inline void make_failure()
    {
      status=statust::FAILURE;
    }
    
    inline void make_success()
    {
      status=statust::SUCCESS;
    }
    
    inline void make_unknown()
    {
      status=statust::UNKNOWN;
    }
    
    inline propertyt():number(0), status(statust::UNKNOWN)
    {
    }
    
    trans_tracet counterexample;
  };

  typedef std::list<propertyt> propertiest;
  propertiest properties;
  
  bool property_failure() const
  {
    for(const auto &p : properties)
      if(p.is_failure()) return true;

    return false;
  }
  
  void report_results();
  
  void show_ldg(std::ostream &out);
  bool make_netlist(netlistt &netlist);  

public:  
  // solvers
  int do_compute_ct();
  int do_dimacs();
  //  int do_cvc4();
  //  int do_smt1();
  //  int do_smt2();
  //  int do_boolector();
  //  int do_mathsat();
  //  int do_yices();
  //  int do_z3();
  int do_sat();
  int do_prover();
  int do_lifter();
};

#endif
