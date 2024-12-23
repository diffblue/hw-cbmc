/******************************************************

Module: Main

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/

// clang-format off
// The order of these matter.
#include <util/cmdline.h>
#include <util/ui_message.h>

#include <ebmc/liveness_to_safety.h>
#include <ebmc/netlist.h>
#include <ebmc/property_checker.h>
#include <ebmc/report_results.h>

#include <trans-netlist/netlist.h>

#include <temporal-logic/ctl.h>
#include <temporal-logic/ltl.h>
#include <temporal-logic/temporal_logic.h>

#include <verilog/sva_expr.h>

#include <algorithm>
#include <iostream>
#include <map>
#include <queue>
#include <set>

#include "minisat/core/Solver.h"
#include "minisat/simp/SimpSolver.h"

#include "dnf_io.hh"
#include "ccircuit.hh"
#include "m0ic3.hh"

#include "ebmc_ic3_interface.hh"
// clang-format off

hsh_tbl htable_lits;
long long gcount = 0;


/*=====================

       D O _ I C 3

  ====================*/
int do_ic3(const cmdlinet &cmdline,
	   ui_message_handlert &ui_message_handler)

{
  return(ic3_enginet(cmdline,ui_message_handler)());
} /* end of function do_ic3 */

bool ic3_supports_property(const exprt &expr)
{
  if(!is_temporal_operator(expr))
    return false;
  else if(expr.id() == ID_AG)
  {
    return !has_temporal_operator(to_AG_expr(expr).op());
  }
  else if(expr.id() == ID_G)
  {
    return !has_temporal_operator(to_G_expr(expr).op());
  }
  else if(expr.id() == ID_sva_always)
  {
    return !has_temporal_operator(to_sva_always_expr(expr).op());
  }
  else
    return false;
}

/*==================================

    O P E R A T O R

   (functionall call reloading)
  =================================*/
int ic3_enginet::operator()()

{


  Ci.init_parameters();
  read_parameters();

  try    {
    auto transition_system =
      get_transition_system(cmdline, message.get_message_handler());

    properties = ebmc_propertiest::from_command_line(
      cmdline, transition_system, message.get_message_handler());

    // possibly apply liveness-to-safety
    if(cmdline.isset("liveness-to-safety"))
      liveness_to_safety(transition_system, properties);

    // make net-list
    message.status() << "Generating Netlist" << messaget::eom;

    netlist = make_netlist(transition_system, properties,
      message.get_message_handler());

    message.statistics() << "Latches: " << netlist.var_map.latches.size()
                         << ", nodes: " << netlist.number_of_nodes()
                         << messaget::eom;

    if(properties.properties.empty())
    {
      message.error() << "no properties" << messaget::eom;
      return 1;
    }

    // No support for assumptions
    for(auto &property : properties.properties)
    {
      if(property.is_assumed())
      {
        message.error() << "no support for assumptions" << messaget::eom;
        return 1;
      }
    }

    std::size_t number_of_properties = 0;

    for(auto &property : properties.properties)
    {
      if(property.is_disabled())
        continue;

      // Is it supported by the IC3 engine?
      if(!ic3_supports_property(property.normalized_expr))
      {
        property.failure("property not supported by IC3 engine");
        continue;
      }

      number_of_properties++;
    }

    if(number_of_properties == 0)
    {
      namespacet ns(transition_system.symbol_table);
      property_checker_resultt result{properties};
      report_results(cmdline, result, ns, message.get_message_handler());
      return result.exit_code();
    }

    const0 = false;
    const1 = false;
    orig_names = false;
    
    // print_nodes();
    // print_var_map(std::cout);
    read_ebmc_input();
    // print_blif3("tst.blif",Ci.N);
    if (cmdline.isset("aiger")) {
      printf("converting to aiger format\n");
      Ci.print_aiger_format();
      exit(0);
    }
    
    //  printf("Constr_gates.size() = %d\n",Ci.Constr_gates.size()); 
    int result = Ci.run_ic3();

    // find the first unknown property
    for(auto &property : properties.properties)
    {
      if(property.is_unknown())
      {
        switch(result)
        {
        case 1: property.refuted(); break;
        case 2: property.proved(); break;
        default: property.failure(); break;
        }
        break;
      }
    }

    {
      property_checker_resultt result{properties};
      namespacet ns(transition_system.symbol_table);
      report_results(cmdline, result, ns, message.get_message_handler());
    }

    return result;
  }
  catch(const std::string &error_str)
  {
    message.error() << error_str << messaget::eom;
    return 1;
  }
  catch(const char *error_msg)    {
    message.error() << error_msg << messaget::eom;
    return 1;
  }
  catch(int)    {
    return 1;
  }
} /* end of function operator */

/* ======================

       R U N _ I C 3

   ====================*/
int CompInfo::run_ic3()
{
  double usrtime0=0.,systime0=0.;
  double usrtime=0.,systime=0.;
 
  
  bool ok = check_init_states();
  assert(ok);
  assign_var_type();
  assign_value();
  get_runtime (usrtime0, systime0);
  int res = mic3();
  get_runtime (usrtime, systime);  

  int ret_val;
  printf("\n");
  switch (res) {
  case 0: {
    printf("property HOLDS\n");  
    if (vac_true) {
      printf("It is vacuously true\n");
      ret_val = 2;
      statistics = false;
      break;
    }
    if (print_inv_flag) 
      print_invariant(print_only_ind_clauses);
    if (print_clauses_flag)
      print_fclauses();
    bool ok = ver_trans_inv();
    if (ok) ret_val = 2;
    else ret_val = 12;
    break;}
  case 1: {
    printf("property FAILED\n");
    form_cex();  
    if (print_cex_flag == 1)
      fprint_cex1();
    else if (print_cex_flag == 2)
      fprint_cex2();
    if (print_clauses_flag) {
      print_invariant(true);
    }
    bool ok = ver_cex();
    if (ok)  ret_val = 1;
    else ret_val = 11;
    break;}
  case 2:
    printf("UNDECided\n");
    ret_val = 3;
    if (print_clauses_flag) 
      print_fclauses();
    break;
  default:
    assert(false);
  }
  if (statistics) {
    printf("*********\n");
    if ((stat_data > 0) && (ret_val < 10)) print_stat();
    printf("total time is %.2f sec.\n",usrtime-usrtime0);
  }
  return(ret_val);
} /* end of function run_ic3 */



/*========================

       M I C 3

   Returns: 
    0 - property holds
    1 - property failed
    2 - undecided

  =======================*/
int CompInfo::mic3()
{

  check_conv_tbl(Pres_svars,Pres_to_next,true);
  check_conv_tbl(Next_svars,Next_to_pres,false);
 
  htable_lits.hsh_init(4*max_num_vars+1);
  form_bad_states();
  form_property();
  if (use_short_prop) form_short_property();
 
  ci_init();
  bool ok = init_st_satisfy_constrs();
  if (!ok) {
    vac_true = true;
    return(0); // property holds
  }
  ok = check_one_state_cex();
  if (!ok) return(1); // property does not hold

  ok = check_two_state_cex();
  if (!ok) return(1);


  if (ctg_flag) form_coi_array();
  tf_lind = 1;
 

  init_lbs_sat_solver();
  init_lgs_sat_solver();
  int ret_val = -1;
 
  while (true) {
    max_num_tfs = tf_lind;
    int res = next_time_frame();
    print_time_frame_stat();
    fflush(stdout);

    if (verbose > 1) {
      print_bnd_sets1();     
    }
  
    if ((res == 0) || (res == 1)) {
      ret_val = res;
      goto FINISH; }

    if (res == 3) {
      ret_val = 2;
      goto FINISH;}

    assert(res == 2);
    tf_lind++;
    if (fin_tf > 0) 
      if (tf_lind > fin_tf) {
	ret_val = 2;
	goto FINISH;}
  }
  
 FINISH:
  delete_solver(Lbs_sat);
  delete_solver(Lgs_sat);
  return(ret_val);

} /* end of function mic3 */
