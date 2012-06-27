#include "assumptions.h"
#include <fstream>
//#define DEBUG

ce_testt ce_test;
core_testt core_test;
naive_testt naive_test;
induction_testt induction_test;
induction_testt induction_test_from_scratch;
interpolation_testt interpolation_test;
const char *fn= "coverage_log";
std::ofstream log(fn, std::ios::out);

const char *fn1= "coverage_log_naive";
std::ofstream log_naive(fn1, std::ios::out);

void assumptionst::get_assumptions(std::vector<literalt> &assumptions,
                                   const bmc_mapt &netlist_bmc_map_init,
                                   bool force,
                                   unsigned bound)
{

    //do not change the initial states
    //make the force select zero to disable forcing
  for(std::map< std::string, force_multiplexert>::const_iterator iter = force_selects_node.begin();
      iter != force_selects_node.end(); iter++)
  {  
#ifdef DEBUG
    std::cout << "second is " << (*iter).second.force_select_var << std::endl;
    std::cout << "timeframe size " << netlist_bmc_map_init.timeframe_map[0].size() << std::endl;
#endif
    literalt l = netlist_bmc_map_init.translate(0, literalt((*iter).second.force_select_var, false));
#ifdef DEBUG
    std::cout << "l is " << l.dimacs() << std::endl;
#endif
    assumptions.push_back(l.negation());
  }

    //start forcing  
  for(std::map< std::string, force_multiplexert>::const_iterator iter = force_selects_node.begin();
      iter != force_selects_node.end(); iter++)
    insert_assumption(*iter, assumptions, netlist_bmc_map_init, force, bound);
//TODO: disable forcing aig nodes in tf 0 to prevent changing initial states
//TODO: enable forcing aig nodes in tf bound+1.

  for(std::map< std::string, force_multiplexert>::const_iterator iter = force_selects_latch.begin();
      iter != force_selects_latch.end(); iter++)
    insert_assumption(*iter, assumptions, netlist_bmc_map_init, force, bound);
}

//put a mux xelector in all timeframes as per bound
void assumptionst::insert_assumption(const std::pair<std::string, force_multiplexert> &iter,
                                     std::vector<literalt> &assumptions,
                                     const bmc_mapt &netlist_bmc_map_init,
                                     bool force,
                                     unsigned bound)
{
    std::map<unsigned, force_valuet> ::const_iterator fiter = force_map.find(iter.second.force_select_var);
    if((fiter != force_map.end()) && force)
    {
      for(unsigned c=0; c<bound+1; c++) //note the difference here
      {
//#ifdef DEBUG
        std::cout << "timeframe is " << c << std::endl;
//#endif
        literalt l = netlist_bmc_map_init.translate(c, literalt(iter.second.force_select_var, 
                                                                false));
        assert(!l.sign()); //+ve literal
        
        assumptions.push_back(l); //force sel
#ifdef DEBUG
        std::cout << "var to be forced is " << l.dimacs() << std::endl;
#endif
        l = netlist_bmc_map_init.translate(c, literalt((*fiter).second.force_val_var, 
                                                       false));
        assert(!l.sign());
#ifdef DEBUG        
        std::cout << "value is " << (*fiter).second.force_val << std::endl;
        std::cout << "val var is " << l.dimacs() << std::endl;
#endif
        if((*fiter).second.force_val == ONE) //force to 1
          assumptions.push_back(l); 
        else if((*fiter).second.force_val == ZERO)
          assumptions.push_back(l.negation()); 
        else if((*fiter).second.force_val == NONDET){}
      }
    }
    else
    {
        //set force to 0
      for(unsigned c=0; c<bound+1; c++) //note the difference here
      {  
        literalt l = netlist_bmc_map_init.translate(c, literalt(iter.second.force_select_var, 
                                                                false));
        assert(!l.sign()); 
        assumptions.push_back(l.negation()); //no force //-ve literal
#ifdef DEBUG
        std::cout << "var NOT to be forced is " << l.negation().dimacs() << std::endl;
#endif
      }
      
    }
}

void assumptionst::get_assumptions_for_timeframe(std::vector<literalt> &assumptions,
                                                 const bmc_mapt &netlist_bmc_map_init,
                                                 bool force,
                                                 unsigned c)
{

    //do not change the initial states
    //make the force node selects zero to disable forcing
  if(c == 0)
  {  
    for(std::map< std::string, force_multiplexert>::const_iterator iter = force_selects_node.begin();
        iter != force_selects_node.end(); iter++)
    {
      literalt l = netlist_bmc_map_init.translate(0, literalt((*iter).second.force_select_var, false));
#ifdef DEBUG
      std::cout << "second is " << (*iter).second.force_select_var << std::endl;
      std::cout << "timeframe size " << netlist_bmc_map_init.timeframe_map[0].size() << std::endl;
      std::cout << "l is " << l.dimacs() << std::endl;
#endif
      assumptions.push_back(l.negation());
    }
  }
  else     //start forcing
    insert_assumption_for_timeframe(force_selects_node, assumptions, netlist_bmc_map_init, c, force);

  insert_assumption_for_timeframe(force_selects_latch, assumptions, netlist_bmc_map_init, c, force);
}


//put all mux xelector in a given timeframe
void assumptionst::insert_assumption_for_timeframe(const std::map<std::string, force_multiplexert> &given_map,
                                                   std::vector<literalt> &assumptions,
                                                   const bmc_mapt &netlist_bmc_map_init,
                                                   unsigned c,
                                                   bool force)
{
  for(std::map< std::string, force_multiplexert>::const_iterator iter = given_map.begin();
      iter != given_map.end(); iter++)
  {
    std::map<unsigned, force_valuet> ::const_iterator fiter = force_map.find((*iter).second.force_select_var);
    if((fiter != force_map.end()) && force)
    {
      literalt l = netlist_bmc_map_init.translate(c, literalt((*iter).second.force_select_var, 
                                                              false));
      assert(!l.sign()); //+ve literal

      assumptions.push_back(l); //force sel
#ifdef DEBUG
      std::cout << "var to be forced is " << l.dimacs() << std::endl;
#endif
      l = netlist_bmc_map_init.translate(c, literalt((*fiter).second.force_val_var, 
                                                     false));
      assert(!l.sign());
#ifdef DEBUG
      std::cout << "value is " << (*fiter).second.force_val << std::endl;
      std::cout << "val var is " << l.dimacs() << std::endl;
#endif
      if((*fiter).second.force_val == ONE) //force to 1
        assumptions.push_back(l); 
      else if((*fiter).second.force_val == ZERO)
        assumptions.push_back(l.negation()); 
      else if((*fiter).second.force_val == NONDET){}
    }
    else
    {
      literalt l = netlist_bmc_map_init.translate(c, literalt((*iter).second.force_select_var, 
                                                              false));
      assert(!l.sign()); 
      assumptions.push_back(l.negation()); //no force //-ve literal
#ifdef DEBUG
        std::cout << "var NOT to be forced is " << l.negation().dimacs() << std::endl;
#endif

    }
  }
}

interpolation_testt::interpolation_testt(){
    total_tests = 0;
    fixedpoint =0;
    nondet_fixedpoint =0;
    counterexample = 0;
    reused_counterexample = 0;
}

void interpolation_testt::print()
  {
    log << "INTERPOLATION TEST\n";
    log << "Total tests " << total_tests << std::endl;
    log << "Number of primary NOTcovered latches " << fixedpoint << std::endl;
    log << "Number of secondary NOTcovered latches " << nondet_fixedpoint << std::endl;
    log << "Number of PRIMARY COVERED latches=" << counterexample << std::endl;
    log << "Number of SECONDARY COVERED latches=" << reused_counterexample << std::endl;
    log << "Total time spent =" << time2string(total_time) << std::endl;
  }

induction_testt::induction_testt(){
    total_tests = 0;
    inductive =0; 
    nondet_inductive =0; 
    non_inductive = 0;
}


void induction_testt::print()
  {
    log << "INDUCTION TEST\n";
    log << "Total tests " << total_tests << std::endl;
    log << "Number of primary inductive latches=" << inductive << std::endl;
    log << "Number of Secondary inductive latches=" << nondet_inductive << std::endl;
    
    log << "Number of UNKNOWN latches=" << non_inductive << std::endl;
    log << "Total time spent =" << time2string(total_time) << std::endl;
  }

ce_testt::ce_testt(){
    counterexample = 0;
    reused_counterexample = 0;
}

void ce_testt::print()
  {
    log << "CE TEST\n";
    log << "Number of PRIMARY COVERED latches=" << counterexample << std::endl;
    log << "Number of SECONDARY COVERED latches=" << reused_counterexample << std::endl;
    log << "Total time spent =" << time2string(total_time) << std::endl;
  }

void core_testt::print()
  {
    log << "CORE TEST\n";
    log << "Number of NOTCOVERED latches =" << not_covered << std::endl;
    log << "Total time spent =" << time2string(total_time) << std::endl;
  }

naive_testt::naive_testt(){
    total_tests = 0;
    fixedpoint =0;
    nondet_fixedpoint =0;
    counterexample = 0;
    reused_counterexample = 0;
}

void naive_testt::print()
  {
    log_naive << "NAIVE TEST\n";
    log_naive << "Total tests " << total_tests << std::endl;
    log_naive << "Number of primary NOTcovered latches " << fixedpoint << std::endl;
    log_naive << "Number of secondary NOTcovered latches " << nondet_fixedpoint << std::endl;
    log_naive << "Number of PRIMARY COVERED latches=" << counterexample << std::endl;
    log_naive << "Number of SECONDARY COVERED latches=" << reused_counterexample << std::endl;
    log_naive << "Total time spent =" << time2string(total_time) << std::endl;
  }
