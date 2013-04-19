/*******************************************************************\

Module: VCEGAR Loop

Author: Himanshu Jain
        Daniel Kroening


Date: June 2003

\*******************************************************************/

#include <i2string.h>
#include <iostream>
#include <time_stopping.h>
#include <fstream>

#include <xml.h>

#include <smvlang/expr2smv.h>

#include "vcegar_loop.h"
#include "abstract_expression.h"
#include "vcegar_util.h"
#include "partitioning.h"


/*******************************************************************\

Function: vcegar_loopt::report_success

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vcegar_loopt::report_success()
{
  status("VERIFICATION SUCCESSFUL");

  switch(ui)
  {
  case ui_message_handlert::OLD_GUI:
    std::cout << "SUCCESS" << std::endl
              << "Verification successful" << std::endl
              << ""     << std::endl
              << ""     << std::endl
              << ""     << std::endl
              << ""     << std::endl;
    break;
    
  case ui_message_handlert::PLAIN:
    break;
    
  case ui_message_handlert::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="SUCCESS";
      std::cout << xml;
      std::cout << std::endl;
    }
    break;
    
  default:
    assert(false);
  }
}

/*******************************************************************\

Function: ebmc_baset::report_failure

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vcegar_loopt::report_failure()
{
  status("VERIFICATION FAILED");

  switch(ui)
  {
  case ui_message_handlert::OLD_GUI:
    break;
    
  case ui_message_handlert::PLAIN:
    break;
    
  case ui_message_handlert::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="FAILURE";
      std::cout << xml;
      std::cout << std::endl;
    }
    break;
    
  default:
    assert(false);
  }
}



/*******************************************************************\

Function: vcegar_loopt::obtain_abstract_property 

  Inputs:

 Outputs:

 Purpose: Abstracts the property according to the set of available predicates

\*******************************************************************/

void vcegar_loopt::obtain_abstract_property()
{
  int initp = 1; //default
  
  if(cmdline.isset("init-pred"))
    initp=atoi(cmdline.getval("init-pred"));
  
  assert(initp == 1 || initp ==2);

  exprt property(spec.property);

  switch(initp) 
    {
    case 1: 
	abstract_expression(predicates, property, 1);
	break;
    case 2: 
	abstract_expression(predicates, property, 2);
	break;
    default:
      throw "Illegal value for initp";
    }
  
  abstractor.abstract_trans.abstract_spec.property_string 
    = spec.property_string;

  
  if (verbose)
    status("Property string "+abstractor.abstract_trans.abstract_spec.property_string);
  
  
  abstractor.abstract_trans.abstract_spec.property 
    = property;

}

/*******************************************************************\

Function: vcegar_loopt::print_stats

  Inputs:

 Outputs:

 Purpose: Prints stats on succesful/unsuccesful run of VCEGAR

\*******************************************************************/

void vcegar_loopt::print_stats(
  unsigned iterations, 
  const fine_timet &start_time,
  const fine_timet &abs_time,
  const fine_timet &mc_time,
  const fine_timet &ref_time) 
{
  status("Machine name");

  status("#No. of iterations done: "+i2string(iterations));
  status("#Max no. of iterations : "+i2string(max_iterations));
  status("#Total number of predicates needed: "+i2string(predicates.size()));
  status("#Partitioning technique: "+i2string(abstractor.partitioning_strategy));
  status("#Total #trans clusters ["+i2string(abstractor.num_trans_clusters)+"] "+
	 "Max trans cluster size ["+i2string(abstractor.max_trans_cluster_size)+"]");
  
  status("#Total time: "+time2string(current_time()-start_time));
  status("#Abstraction time: "+time2string(abs_time));
  status("#Abstract model checking time: "+time2string(mc_time));
  status("#Simulation and Refinement time: "+time2string(ref_time));

  //for LaTeX resuts 
  status("#BENCH   &"+time2string(current_time()-start_time)+" & "+
	 time2string(abs_time)+ " & "+time2string(mc_time)+" & "+
	 time2string(ref_time)+ " & "+i2string(predicates.size())+"/"+
	 i2string(abstractor.max_trans_cluster_size)+ " & "+i2string(iterations)+
	 " & "+i2string(iteration_spurious_transition)+"/"+
	 i2string(iteration_weakest_precondition));
}

/*******************************************************************\

Function: vcegar_loopt::additional_stats

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void vcegar_loopt::additional_stats(
  const fine_timet &spurious_trans_time,
  const fine_timet &bmc_time,
  const fine_timet &unsat_time,
  const fine_timet &wp_time) 
{
  status("#Breakup of simulation and refinement time:");

  status("#Simulating abstract transition steps: "+time2string(spurious_trans_time));
  status("#Simulating the counterexample using BMC: "+time2string(bmc_time));
  status("#Simulating the spurious counterexample for unsat core: "+time2string(unsat_time));
  status("#Obtaining word level predicates using simplified weakest pre-conditions: "+
	 time2string(wp_time));
  abstractor.out_stats(std::cout); 
  simulator.out_stats(std::cout); 
  status("#Refinement due to spurious transition: "+i2string(iteration_spurious_transition));
  status("#Refinement due to weakest pre-conditions: "+i2string(iteration_weakest_precondition)+" and "+
	 i2string(iteration_weakest_precondition_extra));


}

/*******************************************************************\

Function: vcegar_loopt::go

  Inputs:

 Outputs:

 Purpose: execute the VCEGAR loop

\*******************************************************************/

void vcegar_loopt::go()
{
  status("*** Starting Verilog CEGAR Loop ***");
     
  fine_timet start_time=current_time();
  fine_timet abs_time=0; //for creating abstraction 
  fine_timet mc_time=0; //for modelchecking
  fine_timet ref_time=0; //for simulation and refinement

  fine_timet time_spurious_trans = 0; //time taken when simulating each transition seperately
  fine_timet time_doing_bmc = 0; //time taken for performing BMC
  fine_timet time_doing_unsat_core = 0; //time taken when performing unsat core calculation for an 
                                        //spurious counterexample
  fine_timet time_doing_wp = 0; //time taken to obtain new predicates

  unsigned old_counterexample_length = 0; //so that we do not do BMC if an abstract 
                                          //counterexample of same length comes again
                                          //useful if noconstrain is given

  if (use_siege)
    throw "Support for --siege option removed\n";

  //check states marked in unsat proof correspond to spurious transitions
  if(refine1) 
    throw "--refine1 option no longer supported\n";

  // New code passing network information around.
  network_infot network(
    concrete_trans.trans_expr.invar(), 
    concrete_trans.trans_expr.trans(),
    concrete_trans.var_map, context);

  if(verbose)
    status("Network built"); 

  #ifdef DEBUG   
  network.print_members();
  network.print_next_state_function_cache();
  #endif

  // Create initial abstraction
  if(spec.preds_from_property.empty())
    throw "No predicates to start the CEGAR loop";

  refiner.init_preds(predicates, spec.preds_from_property);

  if(verbose)
    std::cout << predicates;

  //Add the user provided predicates if --pred option is given
  if(cmdline.isset("pred")) 
  { 
    refiner.init_preds(predicates, user_provided_preds);
      
    if(verbose)
    {
      std::cout << "Added the predicates from the predicate file\n";
      std::cout << predicates;
    }
  }

  // Express property in terms of abstract variables
  obtain_abstract_property();

  unsigned iteration=0;
  create_abstraction = true;

  concrete_counterexamplet concrete_counterexample;

  while(true) 
  {
    if(!unbounded_cegar_iterations && iteration==max_iterations)
    {
      error("Try increasing maximum number of iterations");
      print_mapping();
      return;
    }
      
    iteration++;
      
    assert(unbounded_cegar_iterations || iteration <= max_iterations);

    status("VCEGAR CEGAR Loop Iteration "+i2string(iteration));

    // Abstract

    if(create_abstraction) 
    {
      fine_timet abs_start_time=current_time();
      
      abstractor.calc_abstraction(
        predicates,
        concrete_trans,
        context, 
        network,
        pred_id_clusters);

        abs_time+=current_time()-abs_start_time; 
    }
    else 
    {
      if(verbose)
        status("Using newly generated constrains, from abstract counterexample");
    }

    //abstract counterexample 
    abstract_counterexamplet abstract_counterexample;
      
    // Verify
    fine_timet mc_start_time=current_time();
    
    if(verbose)
      status("Calling modelchecker\n");

    bool pass =
      modelchecker.check(
        abstractor.abstract_trans,
        abstract_transition_constrains,
        weakest_precondition_constrains,
	abstract_initial_constrains,
        abstract_counterexample);
      
    mc_time += current_time() - mc_start_time; 

    if(pass)
    {
      //result("VERIFICATION SUCCESSFUL"); 
      report_success();
      print_stats(iteration, start_time, abs_time, mc_time, ref_time);
      additional_stats(time_spurious_trans, time_doing_bmc, 
                       time_doing_unsat_core,  time_doing_wp);
      print_mapping();
      break;
    }

    // Refine

    fine_timet ref_start_time=current_time();

    bool contains_spurious_abstract_steps = false;

    if(constrain)
    {
      spurious_abstract_stepst spurious_abstract_steps;

      fine_timet time_spurious_trans_start=current_time();


      if (verbose)
	status("Calling check abstract steps standard");
          
      contains_spurious_abstract_steps = 
	simulator.check_abstract_steps_standard
	(context,
	 concrete_trans,
	 abstract_counterexample,
	 predicates,
	 abstract_transition_constrains,
	 pred_id_clusters,
	 verbose,
	 true);


	
      if(verbose)
	std::cout << "contains_spurious_abstract_steps "
		  <<contains_spurious_abstract_steps<< "\n";

      #ifdef DEBUG
      partitioningt partition_dummy;
      partition_dummy.print_clusters(pred_id_clusters) ; 
      #endif


      time_spurious_trans += current_time() - time_spurious_trans_start; 
	   	  	    
      if (contains_spurious_abstract_steps && !generate_clusters) 
      {
	iteration_spurious_transition++;
        //refine abstract model without adding predicates
        //we won't create new abstraction.
        create_abstraction = false;
      }
    }
	  
    if(!contains_spurious_abstract_steps || !constrain) 
    {
      //Simulate the entire abstract counterexample only if each of the invidual
      //steps are not spurious. (done by check_abstract_steps above)
      // OR if given noconstrain option.

      fine_timet time_doing_bmc_start = current_time();

      bool is_spurious_using_bmc = true; 
	      

      if (old_counterexample_length < abstract_counterexample.size())
      {
        if (verbose)
          std::cout << "Checking spurious using BMC for length = "
                    << abstract_counterexample.size()<<"\n";
        
        is_spurious_using_bmc = 
          simulator.check_spurious_using_bmc(context,
                                             concrete_trans,
                                             abstract_counterexample,
                                             spec.property,
					     concrete_counterexample,
                                             verbose,
                                             true);
      }

      time_doing_bmc += current_time() - time_doing_bmc_start;

      if(!is_spurious_using_bmc)
      {
	//show the counterexample
	messaget message(get_message_handler());
	show_trans_trace(concrete_counterexample, 
			 message,
			 namespacet(context),
			 ui);


        // counterexample is not spurious. 
        //result("Property does NOT hold!");
	report_failure();
        print_stats(iteration, start_time, abs_time, mc_time, ref_time);
        
        additional_stats (time_spurious_trans, time_doing_bmc, 
                            time_doing_unsat_core,  time_doing_wp);
        print_mapping();
        break;
      }

      // remember that we did bmc-like computation for this length, and found that 
      //there is no real counterexample of this length

      old_counterexample_length = abstract_counterexample.size();

      // it is spurious, refine by adding predicates

      if(verbose)
        std::cout <<"Encountered a spurious counterexample\n";
    
      std::vector<std::set<unsigned> > imp_preds_per_state;

      //use unsat cores to determine predicates whose
      // weakest pre-condition needs to be taken

      fine_timet time_doing_unsat_core_start = current_time();
       

      simulator.check_spurious_using_simulation_standard
	(context,
	 concrete_trans,
	 abstract_counterexample,
	 predicates,
	 imp_preds_per_state,
	 true,
	 verbose,
	 true) ; 


      time_doing_unsat_core += current_time() - time_doing_unsat_core_start; 

      unsigned num_wp_constraints_before = weakest_precondition_constrains.size();
      unsigned num_preds_after           = predicates.size();
      unsigned num_wp_constraints_after  = weakest_precondition_constrains.size();
      unsigned num_preds_before          = predicates.size();
      unsigned num_abs_init_constraints  = abstract_initial_constrains.size();

      fine_timet time_doing_wp_start = current_time();
      num_wp_constraints_before =  weakest_precondition_constrains.size();
      
      iteration_weakest_precondition++;
      
      if (abstract_counterexample.size() > 1)
	refiner.spurious_ce(predicates,
			    concrete_trans,
			    abstract_counterexample,
			    context,
			    spec.property, 
			    network,
			    imp_preds_per_state,
			    weakest_precondition_constrains,
			    false);
      else
	add_initial_state_constrain(abstract_counterexample, 
				    imp_preds_per_state, 
				    abstract_initial_constrains);

      num_preds_after = predicates.size();
      
      num_wp_constraints_after =  weakest_precondition_constrains.size();
      
      time_doing_wp += current_time() - time_doing_wp_start;
      
      if((num_preds_after == num_preds_before) && 
         (num_wp_constraints_after == num_wp_constraints_before) &&
	 (num_abs_init_constraints == abstract_initial_constrains.size()))
	{
	  //try to find more predicates
	  if (abstract_counterexample.size() > 1)
	    {
	      status("Additional predicate generation in iteration "+
		     i2string(iteration));
	      refiner.spurious_ce(predicates,
				  concrete_trans,
				  abstract_counterexample,
				  context,
				  spec.property, 
				  network,
				  imp_preds_per_state,
				  weakest_precondition_constrains,
				  true);
	      iteration_weakest_precondition_extra++;
	    }
	  
	  if (predicates.size() > num_preds_before)
	    create_abstraction = true;
	  else
	    {
	      status("No new predicates/ wp constraints  discovered from refinement in iteration no. "+
		     i2string(iteration));
	      throw "Reached a no difference state \n";
	    }
	}
      else 
	create_abstraction = true;
    }

    ref_time += current_time() - ref_start_time; 

    if(cmdline.isset("more-stats")) 
    { 
      print_stats(iteration, start_time, abs_time, mc_time, ref_time);

      additional_stats (time_spurious_trans, time_doing_bmc, 
                        time_doing_unsat_core,  time_doing_wp);
    }
  }
}

/*******************************************************************\

Function: vcegar_loopt::add_initial_state_constrain

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void vcegar_loopt::add_initial_state_constrain(const abstract_counterexamplet &spurious_counterexample,
					       const std::vector<std::set<unsigned> > &imp_preds_per_state,
					       abstract_initial_constrainst &abstract_initial_constrains)
{
  assert(spurious_counterexample.size() == 1);
  assert(imp_preds_per_state.size() == 1);

  if (imp_preds_per_state[0].empty())
    return;

  const std::set<unsigned> &imp_ipreds = imp_preds_per_state[0];
  abstract_constraintt new_constrain;

  simulator.copy_important_preds(spurious_counterexample[0], imp_ipreds, new_constrain);

  abstract_initial_constrains.insert(new_constrain);
}



/*******************************************************************\

Function: vcegar_loopt::print_mapping

  Inputs:

 Outputs:

 Purpose: prints predicates and boolean vars mapping

\*******************************************************************/

void vcegar_loopt::print_mapping()
{
  if (cmdline.isset("mapping"))
  {
    std::ofstream mapfile("vcegar.map");
    if(mapfile)
      mapfile << predicates;
  }
}
