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

#include <langapi/language_file.h>
#include <solvers/sat/cnf.h>
#include <solvers/stack_decision_procedure.h>
#include <trans-netlist/bmc_map.h>
#include <trans-netlist/netlist.h>
#include <trans-netlist/trans_trace.h>

#include "transition_system.h"

#include <fstream>

class ebmc_baset
{
public:
  ebmc_baset(const cmdlinet &_cmdline,
             ui_message_handlert &_ui_message_handler);
  virtual ~ebmc_baset() { }

  int get_transition_system();
  int get_properties();

protected:
  messaget message;
  const cmdlinet &cmdline;
  language_filest language_files;

  transition_systemt transition_system;

  int preprocess();

  bool get_main();
  bool get_bound();

  // word-level
  int do_word_level_bmc(stack_decision_proceduret &, bool convert_only);
  void word_level_properties(decision_proceduret &);
  int finish_word_level_bmc(stack_decision_proceduret &);

  // bit-level
  int do_bit_level_bmc(cnft &solver, bool convert_only);
  int finish_bit_level_bmc(const bmc_mapt &bmc_map, propt &solver);

  bool parse_property(const std::string &property);
  bool get_model_properties();
  void show_properties();

  bool parse();
  bool parse(const std::string &filename);
  bool typecheck();

  std::size_t bound;

  struct propertyt
  {
  public:
    unsigned number;
    irep_idt name;
    source_locationt location;
    std::string expr_string;
    irep_idt mode;
    exprt expr;
    bvt timeframe_literals;             // bit level
    exprt::operandst timeframe_handles; // word level
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

  bool property_requires_lasso_constraints() const;

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
  int do_show_formula();
};

#endif
