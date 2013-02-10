/*******************************************************************\

Module: Interpolation on netlist

Author: Mitra Purandare

\*******************************************************************/
#include <fstream>
#include "interpolation_netlist.h"
#include "../interpolation/bitlevel/strengthen_interpolant.h"
#include "../interpolation/bitlevel/peripheral.h"
#include "../coverage/coverage.h"

/*******************************************************************\

Function: do_interpolation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

/*int do_coverage(const cmdlinet &cmdline)
{
  interpolationt_netlist interpolation(cmdline);
  interpolation.set_unrolling_type(KEN);
  interpolation.set_coverage(true);  
  interpolation.set_induction(false);
  interpolation.set_minimize(true);  
  return interpolation.do_interpolation();
}
*/
int do_interpolation_netlist(
  const cmdlinet &cmdline)
{
  interpolationt_netlist interpolation(cmdline);
  return interpolation.do_interpolation();
}

/*******************************************************************\

Function: interpolationt::do_interpolation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int interpolationt_netlist::do_interpolation()
{
  fine_timet start_time =current_time();
    // build the model first
  int result=get_model();
  if(result!=-1) return result;

    // do we have any properties?
  if(properties.empty())
  {
    error("no properties");
	  return 1;
  }
    //generate netlist
  make_netlist(working_netlist); 
//  netlist.print(std::cout);
  
    // check the initial state
  result = check_initial_state();
  std::cout << "Time to check initial states = " << time2string(current_time()-start_time) << std::endl;
  result = do_iteration();

  std::cout << "Times including checking initial states\n";
  
  std::cout << "Total time = " << time2string(current_time()-start_time) << std::endl;
  std::cout << "SAT time = " << time2string(sat_time) << std::endl;
  
  std::cout << "Fixed point time = " << time2string(fix_check_time) << std::endl;
  std::cout << "Minimization time = " << time2string(minimization_time) << std::endl;
  return result;
}

int interpolationt_netlist::do_iteration()
{
  fine_timet start_time =current_time();
  int result = -1;
  
  if(result == -1)
  {
      // now do main loop
    iteration_number=0;
    get_bound();
//    bound=2; // start with 2 time frames
    do
    {
      result=iteration();
    }
    while(result==-1);
  }

  std::cout << "Total time for iterations = " << time2string(current_time()-start_time) << std::endl;
  std::cout << "SAT time during iterations = " << time2string(sat_time) << std::endl;
  
  std::cout << "Fixed point time = " << time2string(fix_check_time) << std::endl;
  std::cout << "Minimization time = " << time2string(minimization_time) << std::endl;
  return result;
}

/*******************************************************************\

Function: interpolationt_netlist::check_initial_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int interpolationt_netlist::check_initial_state()
{
  satcheckt satcheck;

  namespacet ns(symbol_table);
  boolbvt solver(ns,satcheck);
    // check if I AND !P is satisfiable

  bmc_mapt netlist_bmc_map_init;

  netlist_bmc_map_init.map_timeframes(working_netlist, 1, satcheck);

  ::unwind(working_netlist, netlist_bmc_map_init, *this, satcheck, true); 

  std::cout << "construct property\n";

  prop_bv.clear();
  unwind_property(
    working_netlist, 
    netlist_bmc_map_init, // timeframes
    *this,     prop_bv,
    satcheck);

  fine_timet sat_start_time=current_time();
  decision_proceduret::resultt dec_result=
    solver.dec_solve();
  sat_time = current_time()-sat_start_time;

  switch(dec_result)
  {
    case decision_proceduret::D_SATISFIABLE:
    {
      result("SAT: bug found. Bound=0");
      result("Iteration 0");
      result("Bound=0");
      show_counterexample(prop_expr_list, prop_bv, *this, satcheck, netlist_bmc_map_init,
                          ns, ui_message_handlert::PLAIN);
      report_failure();
    }
    return 0;
    case decision_proceduret::D_UNSATISFIABLE:
      result("UNSAT: No bug found in initial timeframe");
      break;
    case decision_proceduret::D_ERROR:
      error("Error from decision procedure");
      return 2;

    default:
      error("Unexpected result from decision procedure");
      return 1;
  }
  return -1;
}

/*******************************************************************\

Function: interpolationt_netlist::iteration

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int interpolationt_netlist::iteration()
{
  iteration_number++;

  std::cout << "Iteration " << iteration_number << std::endl;
  std::cout << "Bound= " << bound << std::endl;
  status("Iteration "+i2string(iteration_number)+
         ", bound="+i2string(bound));
        //see if induction succeeds

  namespacet ns(symbol_table);
  interpolatort interpolator;
  boolbvt solver(ns, interpolator);
  solver.equality_propagation=false;
  
  //working_netlist.print(std::cout);
//  netlist.output_dot(std::cout);
  bmc_mapt netlist_bmc_map;
  netlist_bmc_map.map_timeframes(working_netlist, bound+1, interpolator);
  
  interpolator.set_partition_id(1);
  build_partition1(interpolator, netlist_bmc_map);
  solver.clear_cache();

  interpolator.set_partition_id(2);
  build_partition2(interpolator, netlist_bmc_map);
  build_property(interpolator, netlist_bmc_map);

    // solver
  fine_timet sat_start_time=current_time();
  decision_proceduret::resultt dec_result=
    solver.dec_solve();
  sat_time += current_time()-sat_start_time;

  switch(dec_result)
  {
    case decision_proceduret::D_SATISFIABLE:
      if(forward_interpolants.empty())
      {
        result("SAT: bug found. Bound=" + i2string(bound));
        result("Iteration " + i2string(iteration_number));
        result("Bound=" + i2string(bound));
        show_counterexample(prop_expr_list, prop_bv, *this, interpolator, netlist_bmc_map,
                            ns, ui_message_handlert::PLAIN);
        report_failure();
        return 0;
      }
      else
      {
        status("SAT: interpolation failed, increasing bound");
        if(unrolling_type == JAO)
          bound = bound + forward_interpolants.size();
        else
          bound++;
        forward_interpolants.clear();
      }
      break;

    case decision_proceduret::D_UNSATISFIABLE:
      status("UNSAT: getting interpolant, doing widening");
      {
        if(cmdline.isset("strengthen"))
        {
#ifdef HYPER
          std::cout << "support for strengthening interpolants not available for hyper resolution\n";
          assert(0);
#else
//          get_strengthened_interpolant(interpolator);
#endif
        }
        
        else 
          get_interpolant(interpolator, netlist_bmc_map);        
        
        if(reached_fixedpoint())
        {
          
//          std::cout << "fixed point time " << time2string(fix_check_time) << std::endl; 
          return 1;
        }

        if(do_induction)
          return induction_step();
 
//        std::cout << "fixed point time " << time2string(fix_check_time) << std::endl; 
      }
      break;

    case decision_proceduret::D_ERROR:
      error("Error from decision procedure");
      return 2;

    default:
      error("Unexpected result from decision procedure");
      return 3;
  }

  return -1;
}

/*******************************************************************\

Function: interpolationt_netlist::reached_fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool interpolationt_netlist::reached_fixedpoint()
{
  fine_timet st = current_time();

  status("Checking whether we reached a fixed-point");
  if(forward_interpolants.size() == 1)
  {
//    std::cout << "forward_interpolants size 1\n";
//    if(forward_interpolants.back().is_true()) 
//      std::cout << "interpolant is true\n";
    return false;
  }
  
  const bit_interpolantt &new_interpolant = forward_interpolants.back();

  if(new_interpolant.is_false()) 
    return true;

/*  if(new_interpolant.is_true()) 
  {
    std::cout << "interpolant is true\n";
  }
*/
  satcheckt solver;
  namespacet ns(symbol_table);
  bmc_mapt netlist_bmc_map_check;
  netlist_bmc_map_check.map_timeframes(working_netlist, bound+1, solver);

    // "old" set of states
  status("forward_interpolants.size() " + i2string(forward_interpolants.size()));

  literalt l_old = const_literal(false);

  if(unrolling_type == JAO)  //Jao
  {  
    for(unsigned size = 0;
        size < forward_interpolants.size()-1; size++)
    {
      bmc_mapt aig_map;
      literalt l_old_1 = forward_interpolants.at(size).instantiate(aig_map, netlist_bmc_map_check, solver, 0);
      l_old=solver.lor(l_old, l_old_1);
    }
    literalt l_init = const_literal(true);
    
    for(unsigned i=0; i<working_netlist.initial.size(); i++)
      l_init = solver.land(netlist_bmc_map_check.translate(0, working_netlist.initial.at(i)), l_init);

    status("converted initial state");
    l_old=solver.lor(l_old, l_init);    
  }
  else //Ken
  {
    unsigned size = forward_interpolants.size()-2;
	if(forward_interpolants.at(size).is_true())
	l_old = const_literal(true);
       else if (forward_interpolants.at(size).is_false())
	l_old = const_literal(false);
	else {
    bmc_mapt aig_map;
    l_old = forward_interpolants.at(size).instantiate(aig_map, netlist_bmc_map_check, solver, 0);
}
  }
  status("converted old forward_interpolants");
    // "new" set of states
  literalt l_new;
  if(new_interpolant.is_true())
  l_new = const_literal(true);
else if(new_interpolant.is_false())
  l_new = const_literal(false);
else {
  bmc_mapt aig_map;
  l_new = new_interpolant.instantiate(aig_map, netlist_bmc_map_check, solver, 0);
}
  status("converted new interpolant");
    // check if l_new -> l_old = not l_new or l_old == not ( l_new and not l_old)
  solver.l_set_to(l_old, false);
  solver.l_set_to(l_new, true);

  fine_timet sat_start_time=current_time();
  propt::resultt dec_result=
    solver.prop_solve();
  sat_time += current_time()-sat_start_time;
  switch(dec_result)
  {
    case propt::P_SATISFIABLE:
      status("SAT: fixed-point not yet reached");
      fix_check_time += current_time() - st;
      return false;

    case propt::P_UNSATISFIABLE:
      result("UNSAT: fixed-point reached.");
      result("property holds!");
      result("Iteration " + i2string(iteration_number));
      result("Bound=" + i2string(bound));
      fix_check_time += current_time() - st;
      return true;

    default:
      throw "unexpected result from SAT-solver";
  }
}

/*******************************************************************\

Function: interpolationt_netlist::get_interpolant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpolationt_netlist::get_interpolant(
  interpolatort &interpolator,
  bmc_mapt &nbm)
{
    //ok, get the interpolant
  status("current forward_interpolants.size() :: " + i2string(forward_interpolants.size()));
  do_interpolationt do_interpolation(interpolator.get_resolution_proof(), 1);

#ifdef PERPHERALITY

  do_interpolation.get_shared_variables_from(
    interpolator.get_resolution_proof().no_vars+1);

  std::vector<unsigned> global_vars;
//  std::cout <<  "do_interpolation.get_local_variables_1()->size() " << 
//    do_interpolation.get_local_variables_1()->size() << std::endl;
  for(unsigned i=0; i < do_interpolation.get_local_variables_1()->size(); i++)
    if((do_interpolation.get_local_variables_1()->at(i) == true) && 
       (do_interpolation.get_local_variables_2()->at(i) == true))
      global_vars.push_back(i);

  satcheck_peripheralt checkp(interpolator.get_resolution_proof(), 1);
  std::vector<origint> origins;
  origins = checkp.check_peripherality(global_vars);

  std::vector<unsigned> mixed;
  unsigned count = 0;
  for(unsigned i=0; i < origins.size(); i++)
  {
    if(origins.at(i) == MIXED)
    {
      count++;
      mixed.push_back(global_vars.at(i));
    }
  }
  assert(global_vars.size() - mixed.size() == 0);
#endif

  for(unsigned t=0; t <= 1; t++) 
    for(unsigned i=0; i < nbm.timeframe_map[t].size(); i++)
      do_interpolation.local_variables_1[nbm.timeframe_map[t].at(i).solver_literal.var_no()] = true;
  
  for(unsigned t=1; t < nbm.timeframe_map.size(); t++) 
    for(unsigned i=0; i < nbm.timeframe_map[t].size(); i++)
      do_interpolation.local_variables_2[nbm.timeframe_map[t].at(i).solver_literal.var_no()] = true;

  if(unrolling_type == JAO) //Jao
  {
    if(!forward_interpolants.empty())
    {
      assert(last_aig_bmc_map.back().timeframe_map.size() == 1);
      for(unsigned t=0; t < last_aig_bmc_map.back().timeframe_map.size(); t++) 
        for(unsigned i=0; i < last_aig_bmc_map.back().timeframe_map[t].size(); i++)
          do_interpolation.local_variables_1[last_aig_bmc_map.back().timeframe_map[t].at(i).solver_literal.var_no()] = true;
    }
  }  
  else //Ken
  {
    for(unsigned p=0; p < last_aig_bmc_map.size(); p++)
    {
      const bmc_mapt & last_map = last_aig_bmc_map.at(p);
      assert(last_map.timeframe_map.size() == 1);
      for(unsigned t=0; t < last_map.timeframe_map.size(); t++) 
	{ 
       	for(unsigned i=0; i < last_map.timeframe_map[t].size(); i++)
	{
		if(do_interpolation.local_variables_1.size() < last_map.timeframe_map[t].at(i).solver_literal.var_no()+1)
			do_interpolation.local_variables_1.resize(last_map.timeframe_map[t].at(i).solver_literal.var_no()+1, false);
		assert(do_interpolation.local_variables_1.size() >= last_map.timeframe_map[t].at(i).solver_literal.var_no()+1);
    do_interpolation.local_variables_1.at(last_map.timeframe_map[t].at(i).solver_literal.var_no()) = true;

	}	
	} 	
   }	
  }
  
  do_interpolation.given_local_global_vars = true;
  
    //global vars
//  std::cout << "size of variables is :: " << do_interpolation.local_variables_2.size() << std::endl;
//  do_interpolation.local_variables_1 = local_variables_1;
//  do_interpolation.local_variables_2 = local_variables_2;

//#endif    

#if 0
  std::vector<bool> local_root_variables_1;
  std::vector<bool> local_root_variables_2;
  std::vector<bool> local_variables_1;
  std::vector<bool> local_variables_2;
  do_interpolation.local_root_variables_1 = &local_root_variables_1;
  do_interpolation.local_root_variables_2 = &local_root_variables_2;
  do_interpolation.local_variables_1 = &local_variables_1;
  do_interpolation.local_variables_2 = &local_variables_1;
#endif

//  do_interpolation.set_pudlak(true);
  bit_interpolantt inter_ken = do_interpolation.get_interpolant();

//*/
#if 0
#ifdef HYPER
#else
  std::cout << "computing interpolant by Pudlak's rules\n";
  do_interpolationt do_interpolationP(interpolator.get_resolution_proof(), 1);
  do_interpolationP.set_pudlak(true);
  bit_interpolantt inter_pudlak = do_interpolationP.get_interpolant();
  std::cout << inter_pudlak << std::endl;
#endif
#endif
 
#if 0
#ifndef HYPER
  std::cout << "Comparing the interpolants\n";
  satcheck_strengthen_interpolationt st(interpolator.get_resolution_proof());
    //  inter_pudlak.outout_dot(std::cout);
    //  inter_ken.outout_dot(std::cout);  
  st.check_strength(inter_pudlak, inter_ken);
#endif
#endif
    //  getchar();

    //interpolator.get_interpolant(1, 2, forward_interpolants.back());
  status("new forward_interpolants.size() :: " + i2string(forward_interpolants.size()));
  status("interpolant for iteration : "  + i2string(iteration_number) + "bound : " + i2string(bound));
//  std::cout << "size of interpolant " << inter_ken.aig.number_of_nodes() << std::endl;
//  std::cout << forward_interpolants.back().aig << std::endl;
  
//need to create a new aig with netlist variables

  std::cout << inter_ken << std::endl;  
  std::cout << "printed ken\n";
  if(inter_ken.is_false()) 
{
   forward_interpolants.push_back(inter_ken);
   std::cout << "interpolant is false\n";
 return;
} if(inter_ken.is_true()){
  
  std::cout << "interpolant is true\n";
   forward_interpolants.push_back(inter_ken);
return; 
}

  bit_interpolantt inter_netlist = inter_ken.map_from_timeframe(nbm, 1);
#if DEBUG
  if(!check_partition_one_implies_interpolant(inter_netlist) ||
     !check_partition_two_and_interpolant(inter_netlist))
  {
    std::cout << "KEN NOT CORRECT\n";
    assert(0);
  }
#endif
  forward_interpolants.push_back(inter_netlist);

  
//  std::cout << inter_netlist << std::endl;  

  if(minimize_interpolant)
  {
    std::cout << "old size of interpolant " << 
      forward_interpolants.back().aig.number_of_nodes() << std::endl;
    std::cout << "total number of variables " << 
      interpolator.no_variables() << std::endl;

    
    std::cout << "do_interpolation.no_primary_vars_in_interpolant() " << 
      do_interpolation.no_primary_vars_in_interpolant() << std::endl;


/*#ifdef DEBUG
    const char *fn = "aig_minimizer_log";
    std::ofstream ofn(fn, std::ios::out);
    minimizert minimizer(forward_interpolants.back(), do_interpolation.no_primary_vars_in_interpolant(), 0, ofn);
#else
    minimizert minimizer(forward_interpolants.back(), do_interpolation.no_primary_vars_in_interpolant(), 0);
    
//                         forward_interpolants.back().aig.number_of_nodes() - do_interpolation.no_primary_vars_in_interpolant());
#endif

    fine_timet stime = current_time();
    
    minimizer.minimize();
    std::cout << "simulation time " << time2string(minimizer.simulation_time) << std::endl;
    std::cout << "sat time " << time2string(minimizer.sat_time) << std::endl;
    std::cout << "number of satchecks " << minimizer.sat_checks << std::endl;
    std::cout << "conversion time " << time2string(minimizer.conversion_time) << std::endl;
    std::cout << "partition time " << time2string(minimizer.partition_time) << std::endl;    
    std::cout << "total time for minimizing " << time2string(current_time() - stime) << std::endl;
    minimization_time += current_time() - stime; 

#ifdef DEBUG
    ofn.close();
#endif
*/
//    std::cout << "new size of interpolant " << 
//      forward_interpolants.back().aig.number_of_nodes() << std::endl;
  }
  
}

/*******************************************************************\

Function: interpolationt_netlist::build_partition1

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpolationt_netlist::build_partition1(
  interpolatort &interp,
  bmc_mapt &nbm)
{
  status("build_partition1");
  ::unwind(working_netlist, nbm, *this, interp, false, 0);

  if(forward_interpolants.empty())
  {
    status("init when no interpolant");
    for(unsigned i=0; i<working_netlist.initial.size(); i++)
      interp.l_set_to(nbm.translate(0, working_netlist.initial.at(i)), true);
    
  }
  else
  {
    if(unrolling_type == JAO)// Jao
    {
    
      bvt or_bv;
      last_aig_bmc_map.clear();
      bmc_mapt last_map;
      literalt l_old_1 = forward_interpolants.back().instantiate(last_map, nbm, interp, 0);
      last_aig_bmc_map.push_back(last_map);      
      or_bv.push_back(l_old_1);

      interp.lcnf(or_bv);
    }
    else //Ken
    {
      status("init with interpolant");
      bvt or_bv;
      literalt l_init = const_literal(true);
      
      for(unsigned i=0; i<working_netlist.initial.size(); i++)
      {
        literalt l = nbm.translate(0, working_netlist.initial.at(i));
        l_init = interp.land(l_init, l);
      }
      or_bv.push_back(l_init);
      
      last_aig_bmc_map.clear();
      for(unsigned i=0; i < forward_interpolants.size(); i++)
      {
        bmc_mapt last_map;
        if(forward_interpolants.at(i).is_true())	{
	   literalt y = const_literal(true);
	or_bv.push_back(y);

        }
	else if (forward_interpolants.at(i).is_false())
{
            literalt y = const_literal(false);
or_bv.push_back(y);

}
	else
{
        literalt l_old = forward_interpolants.at(i).instantiate(last_map, nbm, interp, 0);
        last_aig_bmc_map.push_back(last_map);
        or_bv.push_back(l_old);
} 
     }
      interp.lcnf(or_bv);      
    }
    
  }
  

  status("build_partition1 done");
}

/*******************************************************************\

Function: interpolationt_netlist::build_partition2

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpolationt_netlist::build_partition2(
  interpolatort &interp,
  bmc_mapt &nbm)
{
  status("build_partition2");
//  unsigned no_timeframes=bound+1;
  unsigned no_timeframes=bound+1;

    // unwinding for frames 1,..,bound
  for(unsigned c=1; c<no_timeframes; c++) //note the difference here
  {
    ::unwind(working_netlist, nbm, *this, interp, false, c);
  }
  
  status("build_partition2 done");
}

/*******************************************************************\

Function: interpolationt_netlist::build_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void interpolationt_netlist::build_property(
  interpolatort &interp,
  bmc_mapt &nbm)
{
  status("build_property");

  unsigned no_timeframes=bound+1;
  unsigned start;

  if(!cmdline.isset("start"))
  {
//    warning("using default start for property building");
    start=1;
  }
  else
  {
    start=atoi(cmdline.getval("start"));
    if(start == 0)
      start = no_timeframes-1;      
  }
  if(start > no_timeframes-1)
  {
    error("start > bound, reduce the value of start\n");
  }

  prop_bv.clear();
  
  bvt all_prop_bv;

  for(unsigned p_no=0; p_no<working_netlist.properties.size(); p_no++)
  {
    prop_bv.push_back(bvt());
    unsigned c = 0;
    for(; c<no_timeframes-1; c++)
    {
      if(c>=start)
      {
        literalt l = nbm.translate(c, working_netlist.properties[p_no]);
        prop_bv.back().push_back(l);
        all_prop_bv.push_back(l);
      }
      else
        prop_bv.back().push_back(const_literal(true));
    }

      // claim: time frame k
    {
        // c = bound
      literalt l = nbm.translate(c, working_netlist.properties[p_no]);
      prop_bv.back().push_back(l);
      all_prop_bv.push_back(l);
    }
  }

  literalt temp = const_literal(true);
  for(unsigned p = 0; p < all_prop_bv.size(); p++)
    temp = interp.land(temp, all_prop_bv.at(p));
  
  interp.l_set_to(temp, false);
  status("build_property done");
}

/*******************************************************************\

Function: interpolationt_netlist::build_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
int interpolationt_netlist::induction_step()
{
  status("Induction Step");

  namespacet ns(symbol_table);
  interpolatort satcheck;
  boolbvt solver(ns, satcheck);
  
  bmc_mapt netlist_bmc_map_induction;
  netlist_bmc_map_induction.map_timeframes(working_netlist, bound+1, satcheck);

    // *no* initial state
  status("instantiating trans");
  ::unwind(working_netlist, netlist_bmc_map_induction, *this, satcheck, false, 0);
  build_partition2(satcheck, netlist_bmc_map_induction);

  unsigned no_timeframes=bound+1;

  for(unsigned p=0; 
      p<working_netlist.properties.size();
      p++)
  {

      // assumption: time frames 0,...,k-1
    for(unsigned c=0; c<no_timeframes-1; c++)
      solver.prop.l_set_to(netlist_bmc_map_induction.translate(c, working_netlist.properties[p]), true);
    
      // claim: time frame k
    {
      literalt t = netlist_bmc_map_induction.translate(no_timeframes-1, working_netlist.properties[p]);
      solver.prop.l_set_to(t, false);
    }    
  }

    //  build_property(solver);
  fine_timet sat_start_time=current_time();
  decision_proceduret::resultt dec_result=
    solver.dec_solve();
  sat_time += current_time()-sat_start_time;
  switch(dec_result)
  {
    case decision_proceduret::D_SATISFIABLE:
      result("SAT: inductive proof failed, k-induction is inconclusive");
      break;

    case decision_proceduret::D_UNSATISFIABLE:
      result("UNSAT: inductive proof successful.");
      result("property holds!");
      result("Iteration " + i2string(iteration_number));
      result("Bound=" + i2string(bound));
      return 1;
      break;

    case decision_proceduret::D_ERROR:
      error("Error from decision procedure");
      return 2;

    default:
      error("Unexpected result from decision procedure");
      return 3;
  }
  return -1;
}

#if 0 
#ifndef HYPER
void interpolationt_netlist::get_strengthened_interpolant(
  interpolatort &interpolator)
{
  
  satcheck_strengthen_interpolationt st(interpolator.get_resolution_proof(), 1);
  bit_interpolantt i_strong = st.get_interpolant();

  forward_interpolants.push_back(i_strong);

  bmc_mapt bmc_map_inter;
  netlist_bmc_map.build_bmc_map(working_netlist, bmc_map_inter);
  map_from_timeframe(bmc_map_inter,forward_interpolants.back().aig, 1);

  if(minimize_interpolant)
  {
#ifdef VERBOSE
    std::cout << "old number of nodes " << forward_interpolants.back().aig.number_of_nodes() << std::endl;
    std::cout << "number of primary variables in the interpolant " << " " << do_interpolation.no_primary_vars_in_interpolant() << std::endl;
    std::cout << "total number of variables in the interpolant " << " " << interpolator.no_variables() << std::endl;
#endif

#ifdef DEBUG
    const char *fn = "aig_minimizer_log";
    std::ofstream ofn(fn, std::ios::out);
    minimizert minimizer(forward_interpolants.back(), st.no_primary_vars_in_interpolant(), 32, ofn);
#else
    minimizert minimizer(forward_interpolants.back(), st.no_primary_vars_in_interpolant(), 32);
#endif
    minimizer.minimize();

    std::cout << "simulation time " << time2string(minimizer.simulation_time) << std::endl;
    std::cout << "sat time " << time2string(minimizer.sat_time) << std::endl;
    std::cout << "conversion time " << time2string(minimizer.conversion_time) << std::endl;
    std::cout << "partition time " << time2string(minimizer.partition_time) << std::endl;    
#ifdef DEBUG
    ofn.close();
#endif

#ifdef VERBOSE
    std::cout << "new number of nodes " << forward_interpolants.back().aig.number_of_nodes() << std::endl;
#endif
  }
  
}
#endif
#endif


bool interpolationt_netlist::check_partition_one_implies_interpolant(const bit_interpolantt &current_inter)
{
  namespacet ns(symbol_table);
  interpolatort interpolator;
  boolbvt solver(ns, interpolator);
 
  bmc_mapt bmc_map_temp;
  bmc_map_temp.map_timeframes(working_netlist, bound+1, interpolator);

  build_partition1(interpolator, bmc_map_temp);

  bmc_mapt last_map;
  literalt l_current = current_inter.instantiate(last_map, bmc_map_temp, interpolator, 1);

  interpolator.l_set_to(l_current, false);
  switch(interpolator.prop_solve())
  {
    case propt::P_SATISFIABLE:
      status("sanity one false :: partition1->interpolant=false");
//      throw "interpolant incorrect :: partition1->interpolant is UNSAT";
      return false;
//      assert(0);

    case propt::P_UNSATISFIABLE:
      result("sanity one true :: partition1->interpolant=true");
      return true;
    default:
      throw "unexpected result from SAT-solver";
  } 
}



bool interpolationt_netlist::check_partition_two_and_interpolant(const bit_interpolantt &current_inter)
{
  namespacet ns(symbol_table);
  interpolatort interpolator;
  boolbvt solver(ns, interpolator);

  bmc_mapt bmc_map_temp;
  bmc_map_temp.map_timeframes(working_netlist, bound+1, interpolator);

  build_partition2(interpolator, bmc_map_temp);
  build_property(interpolator, bmc_map_temp);

  bmc_mapt last_map;
  literalt l_current = current_inter.instantiate(last_map, bmc_map_temp, interpolator, 1);

  interpolator.l_set_to(l_current, true);
  switch(interpolator.prop_solve())
  {
    case propt::P_SATISFIABLE:
      status("sanity two true :: p and b = true");
//      throw "interpolant incorrect :: b and p is SAT";
      return false;
    case propt::P_UNSATISFIABLE:
      result("sanity two false :: p and b = false");
      return true;

    default:
      throw "unexpected result from SAT-solver";
  }
}

void interpolationt_netlist::check_invariant()
{
    //check if I -> property

  satcheckt solver;
  bmc_mapt bmc_map;
  bmc_map.map_timeframes(working_netlist, 1, solver); //vars in tf 0 and 1

  literalt l_unwinding = const_literal(true);

  for(unsigned i=0; i<working_netlist.initial.size(); i++)
    l_unwinding = solver.land(
      bmc_map.translate(0, working_netlist.initial[i]), l_unwinding);

  literalt l_approx = const_literal(false);
  std::cout << "size of interpolants " << get_size_of_interpolants() << std::endl;
  for(unsigned i=0; i < get_size_of_interpolants(); i++)
  {
literalt l_old;
   if(get_interpolant(i).is_true())
    l_old = const_literal(true);
else {
    bmc_mapt last_map;
    l_old = (get_interpolant(i)).instantiate(last_map, bmc_map, solver, 0);
}
    l_approx = solver.lor(l_old, l_approx);
  }
  l_unwinding = solver.lor(l_unwinding, l_approx);

  solver.l_set_to(l_unwinding, true);
  
  ::unwind(working_netlist, bmc_map, *this, solver, false);
  
//  std::list<bvt> prop_bv;
  prop_bv.clear();
  ::unwind_property(working_netlist, bmc_map, *this, prop_bv, solver);
//  build_property(solver, bmc_map);

  propt::resultt dec_result = solver.prop_solve();
  namespacet ns(symbol_table);
  
  switch(dec_result)
  {
    case propt::P_SATISFIABLE:
    {
      show_counterexample(*this, solver, bmc_map,
                          ns, ui_message_handlert::PLAIN);
      assert(0);
    }
    break;
    case propt::P_UNSATISFIABLE:
      break;
    default:
      assert(0);
  }
}

