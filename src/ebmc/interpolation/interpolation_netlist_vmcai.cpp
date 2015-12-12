/*******************************************************************	\

Module: Interpolation on netlist

Author: Mitra Purandare

\*******************************************************************/
#include <sstream>
#include <solvers/prop/aig_formula.h>

#include "interpolation_netlist_vmcai.h"
#if 0
/*******************************************************************\

Function: do_interpolation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int do_interpolation_netlist_vmcai(
  const cmdlinet &cmdline)
{
  interpolationt_netlist_vmcai interpolation(cmdline);
  return interpolation.do_forward_backward_reachability();
}

void collect_local_global_variables(
  bool forward, 
  bmc_mapt &bmc_map, 
  std::vector<bool> &local_variable_1, 
  std::vector<bool> &local_variable_2, 
  unsigned bound)
{
  unsigned local1 = forward ? 0 : bound;
  unsigned local2 = forward ? 1 : bound-1;

  bvt &timeframe_1=bmc_map.timeframe_map[local1];
  for(unsigned v=0; v<timeframe_1.size(); v++)
    local_variable_1.at(timeframe_1[v].var_no()) = true;

  bvt &timeframe_2=bmc_map.timeframe_map[local2];
  for(unsigned t=0; t<timeframe_2.size(); t++)
    local_variable_1.at(timeframe_2[t].var_no()) = true;

  for(unsigned t=0; t<=bound; t++)
  {
    if(t == local1)
      continue;
    bvt &timeframe=bmc_map.timeframe_map[t];
    for(unsigned v=0; v<timeframe.size(); v++)
    {
      if(timeframe[v].var_no() == 181)
	    {}
      else
        local_variable_2.at(timeframe[v].var_no()) = true;
    }
  }
}

/*******************************************************************\

Function: interpolationt::do_interpolation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
int interpolationt_netlist_vmcai::do_forward_backward_reachability()
{
  fine_timet start_time =current_time();
  int result=get_model();
  if(result!=-1) return result;

    // do we have any properties?
  if(properties.empty())
  {
    error("no properties");
    return 1;
  }
    // check the initial state
  make_netlist(netlist); 
  result = check_initial_state();
  int forward_result = -1;
  int backward_result = -1;
  backward_iteration_number = 0;
  forward_iteration_number = 0;
  forward_refinement = false;
  backward_refinement = false;
  bound = 1;
  iterations = 0;
  std::cout << "interpolationt_netlist_vmcai :: start :: pushing back " << bound << std::endl;
  forward_fault_locations.push_back(bound);
  backward_fault_locations.push_back(0);
  forward_fixed_point = false;
  backward_fixed_point = false;
  while(result == -1)
  {
    if(forward_result == 3 && backward_result == 3) // both fixed points but no result,  increase bound
    {
      std::cout << "increasing bound\n";
      std::cout << "iterations for bound= " << bound << " : " << iterations << std::endl;
      iterations = 0 ;
      bound++; result = -1;
      forward_fault_locations.clear(); backward_fault_locations.clear();
      std::cout << "Restart :: pushing back " << bound << std::endl;
      forward_fault_locations.push_back(bound); backward_fault_locations.push_back(0);
      forward_refinement = false; backward_refinement = false;
      forward_result = -1;  backward_result = -1;
      forward_interpolants.clear(); backward_interpolants.clear(); //?
    }
    if(forward_result != 3)
    {
      std::cout << "interpolationt_netlist_vmcai::forward iteration\n";
      forward_result = forward_iteration(); 
        //forward_iteration() returns 1 if fixed point with result, 
        //  returns 3 if fixed point but no result, 
        //  returns -1 if no fixed point
      result = forward_result;
      std::cout << "forward_result " << forward_result << std::endl;
      if(forward_result == 3)//fixed point but no result i.e. we applied refinement
	    {
	      forward_fixed_point = true;
	      std::cout << "forward fixed point reached\n";
	      result = check_forward_reachable_states(); //returns 3 if there is a result, -1 otherwise
	      if(result != 3)
          approx_forward_reach_states.push_back(forward_interpolants.back());
          //    else if (forward_fault_locations.size() == 0)
          //	approx_forward_reach_states.push_back(forward_interpolants.back());
	    }
      if(forward_fault_locations.size() == 0){ // this happens when all timeframes are corrected.
        forward_result = 3; //we make forward_result=3 in order to increase bound
      }
    }
    backward_result = 3;
      
      /*      if((result == -1) && backward_result != 3)
              {
              std::cout << "backward iteration\n";
              backward_result = backward_iteration();
              if(backward_result == 3) //fixed point but no result
              {
              backward_fixed_point = true;
              std::cout << "backward fixed point reached\n";
              result = check_backward_reachable_states();
              if(result != 3)
              approx_backward_reach_states.push_back(backward_interpolants.back());
              }
              if(backward_fault_locations.size() == 0)
              backward_result = 3;
              }
              forward_result = 3;
      */
  }
  std::cout << "Total time = " << time2string(current_time()-start_time) << std::endl;
  std::cout << "SAT time = " << time2string(sat_time) << std::endl;
  return result;
}

/*******************************************************************\

Function: interpolationt_netlist::iteration

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int interpolationt_netlist_vmcai::forward_iteration()
{
  forward_iteration_number++;
  iterations++;
  std::cout << "Iteration " << forward_iteration_number << std::endl;
  std::cout << "Bound= " << bound << std::endl;
  status("Iteration "+i2string(forward_iteration_number)+
         ", bound="+i2string(bound));

  namespacet ns(symbol_table);
  interpolatort interpolator;
  boolbvt solver(interpolator);
  solver.equality_propagation=false;
  
  netlist_bmc_map.map_timeframes(netlist, bound+1, interpolator);

  interpolator.set_partition_id(1);
  build_forward_partition1(interpolator);
  solver.clear_cache();

  interpolator.set_partition_id(2);
  build_forward_partition2(interpolator);
  build_forward_property(interpolator);

    //netlist.print_my_way(std::cout);
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
        bmc_mapt bmc_map;
        netlist_bmc_map.build_bmc_map(netlist, bmc_map);
        result("SAT: bug found. Bound=" + i2string(bound));
        result("Iteration " + i2string(forward_iteration_number+backward_iteration_number));
        result("Bound=" + i2string(bound));
        show_counterexample(prop_expr_list, prop_bv, *this, interpolator, bmc_map,
                            ns, ui_message_handlert::PLAIN);
        report_failure();
        std::cout << "returning 0\n";
        return 0;
      }
      else
      {
        return Refine_Interpolant(solver, interpolator, true);
      }
      break;

    case decision_proceduret::D_UNSATISFIABLE:
      status("UNSAT: getting interpolant, doing widening");

      {
        get_interpolant(interpolator, true);
        forward_fault_locations.clear();
        std::cout << "UNSAT::start :: clearing & pushing back " << bound << std::endl;
        forward_fault_locations.push_back(bound);
          /*      if(is_property())
                  {
                  }
          */
        if(reached_fixedpoint(true))
        {
          std::cout << "normal interpolation reached fixed point\n";
          if(!forward_refinement)
            return 1;
          else
            return 3; // no result
        }
      }
      break;
    case decision_proceduret::D_ERROR:
      error("Error from decision procedure");
      std::cout << "Error from decision procedure 2 " << std::endl;
      return 2;

    default:
      error("Unexpected result from decision procedure");
      return 1;
  }

  return -1;
}

/*******************************************************************\

Function: interpolationt_netlist::reached_fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool interpolationt_netlist_vmcai::reached_fixedpoint(
  bool forward)
{
    //  return false;
  status("interpolationt_netlist_vmcai::Checking whether we reached a fixed-point");

  std::vector<aig_formulat> *interpolants = forward ? &forward_interpolants : &backward_interpolants;

  if(interpolants->size() == 1)
  {
    std::cout << "interpolants size 1\n";
    if(interpolants->back().is_true()) 
      std::cout << "interpolant is true\n";
    return false;
  }

  aig_formulat &new_interpolant = interpolants->back();

  if(new_interpolant.is_false()) 
  {
    std::cout << "interpolant is false\n";
    return true;
  }

  satcheckt solver;
  namespacet ns(symbol_table);
  netlist_bmc_mapt netlist_bmc_map_check;
  netlist_bmc_map_check.map_timeframes(netlist, bound+1, solver);

  bmc_mapt bmc_map_inter;
  netlist_bmc_map_check.build_bmc_map(netlist, bmc_map_inter);

    // "old" set of states
  status("interpolants->size() " + i2string(interpolants->size()));

  literalt l_old = union_previous_interpolants(bmc_map_inter, solver, forward);
  status("converted old interpolants");

  literalt l_init = const_literal(true);
  if(forward)
  {
    
    for(unsigned i=0; i<netlist.initial.size(); i++)
      l_init = solver.land(netlist_bmc_map.translate(0, netlist.initial.at(i)), l_init);
//    l_init= netlist_bmc_map.translate(0, netlist.initial);
  }
  
  else
  {
      //collect properties instantiated in timeframe=bound
    bvt all_prop_bv;
    for(unsigned p_no=0; p_no<netlist.properties.size(); p_no++)
    {
      literalt l = netlist_bmc_map.translate(bound, netlist.properties[p_no]);
      all_prop_bv.push_back(l);
    }
    l_init = !solver.land(all_prop_bv);
  }
  std::cout << "performing OR\n";
  l_old=solver.lor(l_old, l_init);
  status("converted initial state");

    // "new" set of states
  unsigned tf = forward ? 0 : bound;
  map_to_timeframe(bmc_map_inter, new_interpolant.aig, tf);
  new_interpolant.add_variables(solver);

  literalt l_new = new_interpolant.convert(solver);
  map_from_timeframe(bmc_map_inter, new_interpolant.aig, tf); 

    //literalt l_app_reach = const_literal(true);
  literalt l_app_reach = intersect_approx_reachable_states(bmc_map_inter, solver, forward);
  l_new = solver.land(l_new, l_app_reach);
  status("converted new interpolant");

    //  check_if_interpolant_reach_intersect(forward);
    //  l_new=solver.lor(l_new, l_old); // we need to add this when we do not add all the 
    //previous interpolants to the initial states
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
      return false;

    case propt::P_UNSATISFIABLE:
      result("UNSAT: fixed-point reached.");
      if(!forward_refinement && !backward_refinement)
      {
        result("property holds!");
        result("Iteration " + i2string(forward_iteration_number+backward_iteration_number));
        result("Bound=" + i2string(bound));
      }
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

void interpolationt_netlist_vmcai::get_interpolant(
  interpolatort &interpolator, 
  bool forward)
{
  std::cout << "get_interpolant interpolationt_netlist_vmcai"; 
    //ok, get the interpolant
    //  status("current interpolants.size() :: " + i2string(interpolants.size()));

    //let us collect local variables here
  bmc_mapt bmc_map_inter;
  netlist_bmc_map.build_bmc_map(netlist, bmc_map_inter);

    //  std::vector<bool> local_variables_1(interpolator.no_variables(),false);
    //  std::vector<bool> local_variables_2(interpolator.no_variables(),false);
    //  collect_local_global_variables(forward, bmc_map_inter, local_variables_1, local_variables_2, bound);

  std::vector<aig_formulat> *interpolants = forward ? &forward_interpolants : &backward_interpolants;

    //  interpolator.get_interpolant(1, 2, interpolants->back(), local_variables_1, local_variables_2);
    //  interpolator.get_interpolant(1, 2, interpolants->back());
    //  interpolants->back().aig.print(std::cout, aig_variable_labelingt());

  do_interpolationt do_interpolation(interpolator.get_resolution_proof(), 1);
  aig_formulat inter = do_interpolation.get_interpolant();
  interpolants->push_back(inter); 

  status("new interpolants->size() :: " + i2string(interpolants->size()));
  status("interpolant for iteration : "  + i2string(forward ? forward_iteration_number : backward_iteration_number) + "bound : " + i2string(bound));

  unsigned tf = forward ? 1 : bound -1;
  map_from_timeframe(bmc_map_inter,interpolants->back().aig, tf);
  if(interpolants->back().is_false()) 
  {
    std::cout << "false interpolant\n";
  }


    /*  if(!cmdline.isset("stop-minimize"))
        {
        minimizert minimizer(interpolants.back(), interpolator.no_variables(), 32);
        minimizer.minimize();
        }
    */
}

/*******************************************************************\

Function: interpolationt_netlist::build_partition1

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpolationt_netlist_vmcai::build_forward_partition1(
  interpolatort &interp)
{
  status("interpolationt_netlist_vmcai::build_partition1");
  ::unwind(netlist, netlist_bmc_map, *this, interp, false, 0);

  if((forward_interpolants.empty()))
  {
    status("init when no interpolant");
    literalt l_init = const_literal(true);
    for(unsigned i=0; i<netlist.initial.size(); i++)
      l_init = interp.land(netlist_bmc_map.translate(0, netlist.initial.at(i)), l_init);
//    std::cout << "init " << netlist_bmc_map.translate(0, netlist.initial).var_no() << " tf " << 0 << std::endl;
    interp.l_set_to(l_init, true);
  }
  else
  {
    bvt or_bv;
    literalt lit_init = const_literal(true);
    for(unsigned i=0; i<netlist.initial.size(); i++)
      lit_init = interp.land(netlist_bmc_map.translate(0, netlist.initial.at(i)), lit_init);
//    literalt lit_init = netlist_bmc_map.translate(0, netlist.initial);
    or_bv.push_back(lit_init);
    
    bmc_mapt bmc_map_inter;
    netlist_bmc_map.build_bmc_map(netlist, bmc_map_inter);
   
    literalt l_prev = union_previous_interpolants(bmc_map_inter, interp, true);
    or_bv.push_back(l_prev);
    
    map_to_timeframe(bmc_map_inter, forward_interpolants.back().aig, 0); 
    forward_interpolants.back().add_variables(interp);
    literalt l_old_1 = forward_interpolants.back().convert(interp);
    map_from_timeframe(bmc_map_inter,forward_interpolants.back().aig, 0); //put it back

    or_bv.push_back(l_old_1);
    interp.lcnf(or_bv);

      /*literalt l_prev = union_previous_interpolants(bmc_map_inter, interp, true);

        map_to_timeframe(bmc_map_inter, forward_interpolants.back().aig, 0); 
        forward_interpolants.back().add_variables(interp);
        literalt l_old_1 = forward_interpolants.back().convert(interp);
        map_from_timeframe(bmc_map_inter,forward_interpolants.back().aig, 0); //put it back

        l_prev = interp.lor(l_prev, l_old_1);
    
        literalt l_app_reach = intersect_approx_reachable_states(bmc_map_inter, interp, true);
        l_old_1 = interp.land(l_prev, l_app_reach);
        or_bv.push_back(l_old_1);
        interp.lcnf(or_bv);
      */
  }

  status("build_partition1 done");
}

/*******************************************************************\

Function: interpolationt_netlist::build_partition2

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpolationt_netlist_vmcai::build_forward_partition2(
  interpolatort &interp)
{
  status("interpolationt_netlist_vmcai::build_partition2");
  unsigned no_timeframes=bound+1;

    // unwinding for frames 1,..,bound+1
  for(unsigned c=1; c<no_timeframes; c++)
    ::unwind(netlist, netlist_bmc_map, *this, interp, false, c);

  status("build_partition2 done");
}

/*******************************************************************\

Function: interpolationt_netlist_vmcai::build_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void interpolationt_netlist_vmcai::build_forward_property(
  interpolatort &interp)
{
  status("interpolationt_netlist_vmcai::build_property");

    //  namespacet ns(symbol_table);
  unsigned no_timeframes=bound+1;

  prop_bv.clear();
  
  bvt all_prop_bv;

  for(unsigned p_no=0; p_no<netlist.properties.size(); p_no++)
  {
    prop_bv.push_back(bvt());
    for(unsigned c=0; c<no_timeframes; c++)
    {
      if(c== 0)
        prop_bv.back().push_back(const_literal(true));
      else
	    {
	      literalt l = netlist_bmc_map.translate(c, netlist.properties[p_no]);
	      std::cout << "property " << l.var_no() << " tf " << c << std::endl;
	      prop_bv.back().push_back(l);
	      all_prop_bv.push_back(l);
	    }
    }
  }
  interp.l_set_to(interp.land(all_prop_bv), false);
  status("build_property done");
}

/*
  bool interpolationt_netlist_vmcai::is_property()
  {
  satcheckt solver;
  namespacet ns(symbol_table);
  boolbvt solverbv(solver);
 
  netlist_bmc_mapt netlist_bmc_map_init;
  netlist_bmc_map_init.map_timeframes(netlist, bound+1, solver);


  bmc_mapt bmc_map_inter;
  netlist_bmc_map_init.build_bmc_map(netlist, bmc_map_inter);
  map_to_timeframe(bmc_map_inter,interpolants.back().aig, 0); 


  interpolants.back().add_variables(solver);
  literalt l_new_inter = interpolants.back().convert(solver);
  std::cout << "interpolant is " << l_new_inter.var_no() << std::endl; 

  std::cout << "added variables\n";
  bvt all_prop_bv;
  for(unsigned p_no=0; p_no<netlist.properties.size(); p_no++)
  {
  literalt l = netlist_bmc_map.translate(0, netlist.properties[p_no]);
  all_prop_bv.push_back(l);
  }
    //  std::cout << interpolants.back().aig << std::endl;
    literalt l_prop = solverbv.prop.land(all_prop_bv);
    std::cout << "and of property " << l_prop.var_no() << std::endl;
    std::cout << "added all variables\n";
      //literalt l_xor = solverbv.prop.lxor(l_andf, l_new_inter);
        //  bvt or_bv;
          //  or_bv.push_back(l_xor);
            //  solverbv.prop.lcnf(or_bv);

              //literalt l_and_1 = solverbv.prop.lor(l_prop, solverbv.prop.lnot(l_new_inter));
                //  literalt l_and_2 = solverbv.prop.lor(solverbv.prop.lnot(l_andf), l_new);
                  //  solverbv.prop.l_set_to(l_and_1, true);
                    //  solverbv.prop.l_set_to(l_and_2, true);

                    std::cout << "solver variables " << solver.no_variables() << std::endl;
                    literalt l_eq = solverbv.prop.lequal(l_prop, l_new_inter);
                    std::cout << "now check\n";
                    solverbv.prop.l_set_to(solverbv.prop.lnot(l_eq), true);
                    std::cout << "now check\n";

                    map_from_timeframe(bmc_map_inter,interpolants.back().aig, 0); 
                    fine_timet sat_start_time=current_time();
                    propt::resultt dec_result=
                    solver.prop_solve();
                    sat_time += current_time()-sat_start_time;
                    switch(dec_result)
                    {
                    case propt::P_SATISFIABLE:
                    result("UNSAT: Interpolant not property.");
                    return false;

                    case propt::P_UNSATISFIABLE:
                    status("SAT: Interpolant is the property");
                    return true;

                    default:
                    throw "unexpected result from SAT-solver";
                    }
                    return false;

                    }
*/
int interpolationt_netlist_vmcai::check_forward_reachable_states()
{
  if(forward_interpolants.back().is_false())
  {
    result("PROPERTY VIOLATED\n");
    return 0;
  }
  std::cout <<  "checking forward reachable states\n";
  namespacet ns(symbol_table);
  satcheckt satcheck;
  boolbvt solver(satcheck);
  unsigned check_bound = 2;
  netlist_bmc_mapt netlist_bmc_map_check;
  netlist_bmc_map_check.map_timeframes(netlist, check_bound, satcheck);

  std::cout << "bmc map done\n";
  ::unwind(netlist, netlist_bmc_map_check, *this, satcheck, false);

  std::cout << "unwindng over\n";
  bmc_mapt bmc_map_check;
  netlist_bmc_map_check.build_bmc_map(netlist, bmc_map_check);
  forward_interpolants.back().aig.add_variables(satcheck);
  map_to_timeframe(bmc_map_check, forward_interpolants.back().aig, 0);
  literalt l_old_1 = forward_interpolants.back().convert(solver.prop);
  map_from_timeframe(bmc_map_check, forward_interpolants.back().aig, 0); 

  literalt l_app_reach = intersect_approx_reachable_states(bmc_map_check, satcheck, true);
    //literalt l_app_reach = const_literal(true);
  l_old_1 = satcheck.land(l_old_1, l_app_reach);
  satcheck.l_set_to(l_old_1, true);

  bvt all_prop_bv;
  for(unsigned p_no=0; p_no<netlist.properties.size(); p_no++)
  {
    for(unsigned new_iter=0; new_iter < check_bound; new_iter++)
    {
      literalt l = netlist_bmc_map.translate(new_iter, netlist.properties[p_no]);
      all_prop_bv.push_back(l);
    }
  }
  literalt l_prop = solver.prop.land(all_prop_bv);
  satcheck.l_set_to(l_prop, false);

  fine_timet sat_start_time=current_time();
  propt::resultt dec_result=
    solver.prop.prop_solve();
  sat_time += current_time()-sat_start_time;
  switch(dec_result)
  {
    case propt::P_SATISFIABLE:
      status("SAT: No Result");
      break;
    case propt::P_UNSATISFIABLE:
      result("UNSAT: property holds!");
      result("Iteration " + i2string(forward_iteration_number+backward_iteration_number));
      result("Bound=" + i2string(bound));
      return 3;

    default:
      throw "unexpected result from SAT-solver";
      return 2;
  }
  return  -1;
}


int interpolationt_netlist_vmcai::Refine_Interpolant(
  boolbvt &solver, 
  interpolatort &interpolator, 
  bool forward)
{
  std::vector<unsigned > *fault_locations = forward ? &forward_fault_locations : &backward_fault_locations; 
  namespacet ns(symbol_table);
  status("SAT::Refine Interpolant");
  if(forward)
    forward_refinement = true;
  else
    backward_refinement = true;
  for(unsigned start_prop = 0 ; start_prop < fault_locations->size(); start_prop++)
    std::cout << fault_locations->at(start_prop) << std::endl;
  std::vector<unsigned> new_fault_locations;// = new std::vector<unsigned>(fault_locations->size() + 1);
  
  unsigned new_check = forward ? 1 : bound -1;
  for(unsigned start_prop = 0 ; start_prop < fault_locations->size(); start_prop++)
  {
    solver.clear_cache(); // is it needed here?
    std::cout << "dhoom start_prop " << start_prop << std::endl;
    std::cout << "applying correction at " << fault_locations->at(start_prop) << std::endl;
    if((fault_locations->size() == bound) && (fault_locations->at(start_prop) == new_check))
    {
      std::cout << "setting partition 1\n"; 
      interpolator.set_partition_id(1); //correction for timeframe 1 gets added in partition 1
    }
    else
    {
      interpolator.set_partition_id(2);
      std::cout << "setting partition 2\n"; //if Timeframe > 1 , correction gets added in partition 2
    }
    bvt all_prop_bv;
    std::list<propertyt>::const_iterator p_it=properties.begin();
    for(unsigned p_no=0; p_no<netlist.properties.size(); p_no++)
    {
      assert(p_it != properties.end());
      if(fault_locations->at(start_prop) == new_check)
	    {
          //no need to build it from scratch since we know the interpolant
	      bmc_mapt bmc_map;
	      netlist_bmc_map.build_bmc_map(netlist, bmc_map);
          //need to be build the property from scratch..
          //how?
	      exprt build_property(p_it->expr);
	      const exprt &p=build_property.op0();
	      exprt tmp(p);
	      messaget message;
	      literalt l = instantiate_convert(interpolator, bmc_map, tmp, new_check, new_check+1, ns, message);
	      all_prop_bv.push_back(l);
	    }
      else
	    {
	      literalt l = netlist_bmc_map.translate(fault_locations->at(start_prop), netlist.properties[p_no]);
	      all_prop_bv.push_back(l);
	      std::cout << "l.var_no() " << l.var_no() << std::endl;
	    }
      p_it++;
    }
    literalt pw = interpolator.land(all_prop_bv);
    std::cout << "pw.var_no() " << pw.var_no() << std::endl;
    interpolator.l_set_to(pw, true);

    std::cout << "property instance " << fault_locations->at(start_prop) << std::endl;
    fine_timet sat_start_time=current_time();
    decision_proceduret::resultt refine_dec_result = solver.dec_solve();
    sat_time += current_time()-sat_start_time;
    switch(refine_dec_result)
    {
      case decision_proceduret::D_SATISFIABLE:
        if(start_prop == fault_locations->size()-1)
        {
          std::cout << "not able to convert a SAT to UNSAT\n";
          assert(0);
        }
        std::cout << "SAT\n";
        break;
      case decision_proceduret::D_UNSATISFIABLE:
        get_interpolant(interpolator, forward); 
        std::cout << "checking fixed point reached\n";
          //	  if(is_property()){}
        if(reached_fixedpoint(forward))
        {
          std::cout << "fixed point reached after " << 
            fault_locations->at(start_prop) << "correction\n";
          return 3;
        }
        if((fault_locations->size() == bound)  && (fault_locations->at(start_prop) == new_check))
            // this means all timeframes are corrected. no more corrections possible
        {
          std::cout << "clearing fault locations\n";
          fault_locations->clear(); //what to do next?? increase bound. we have got back the property
        }
        else
        {
          bool push_one = false;
          std::cout << "start_prop " << start_prop << std::endl;
          std::cout << "new_check " << new_check << std::endl;
          for(unsigned add_prop = 0 ; add_prop <= start_prop; add_prop++)
          {
            std::cout << "fault location at place " << add_prop << " :: " << fault_locations->at(add_prop) << std::endl;
            unsigned to_push =  forward ? fault_locations->at(add_prop)-1 : fault_locations->at(add_prop)+1;
            if(new_check == to_push)
              push_one = true;
            else
              new_fault_locations.push_back(to_push);
              //push them first since we want to correct these timeframes before we correct timeframe k
          }
    
          unsigned new_push = forward ? bound : 0;
          new_fault_locations.push_back(new_push);
          if(push_one)
            new_fault_locations.push_back(new_check); // we correct timeframe 1 in the end
	      
          fault_locations->clear();
          for(unsigned loc = 0; loc < new_fault_locations.size(); loc++)
          {
            std::cout << "new fault locations " << new_fault_locations.at(loc) << std::endl;
            fault_locations->push_back(new_fault_locations.at(loc));
          }
        }
        return -1;
        break;
      case decision_proceduret::D_ERROR:
        std::cout << "Error from decision procedure 4 " << std::endl;
        error("Error from decision procedure");
        return 2;

      default:
        error("Unexpected result from decision procedure");
        return 1;
    }
  }
  return 2;
}

literalt interpolationt_netlist_vmcai:: intersect_approx_reachable_states(
  bmc_mapt &bmc_map_inter, 
  satcheckt &solver, 
  bool forward)
{
  std::vector<aig_formulat> *approx_reach_states = forward ? &approx_forward_reach_states : &approx_backward_reach_states;
  std::cout << "approximations " << approx_reach_states->size() << std::endl;
  unsigned tf = forward ? 0 : bound;

  literalt l_new = const_literal(true);
  for(unsigned ffp=0; ffp<approx_reach_states->size(); ffp++)
  {
    map_to_timeframe(bmc_map_inter,approx_reach_states->at(ffp).aig, tf); //get reachable states in timeframe 1
    approx_reach_states->at(ffp).add_variables(solver);
    literalt l_prev_reach = approx_reach_states->at(ffp).convert(solver);	
    l_new = solver.land(l_new, l_prev_reach);
    map_from_timeframe(bmc_map_inter,approx_reach_states->at(ffp).aig, tf); //put them back
  }
  return l_new;
}

literalt interpolationt_netlist_vmcai:: union_previous_interpolants(
  bmc_mapt &bmc_map_inter, 
  satcheckt &solver, 
  bool forward)
{
  std::vector<aig_formulat> *interpolants = forward ? &forward_interpolants : &backward_interpolants;
  unsigned tf = forward ? 0 : bound;

  literalt l_old = const_literal(false);
  for(unsigned size = 0; size < interpolants->size()-1; size++) //skip the latest interpolant
  {
    map_to_timeframe(bmc_map_inter,interpolants->at(size).aig, tf); 
    interpolants->at(size).add_variables(solver);

    literalt l_old_1 = interpolants->at(size).convert(solver);
    l_old=solver.lor(l_old, l_old_1);

    map_from_timeframe(bmc_map_inter,interpolants->at(size).aig, tf); 
  }
  return l_old;
}


int interpolationt_netlist_vmcai::backward_iteration()
{
  backward_iteration_number++;
  iterations++;
  std::cout << "Iteration " << backward_iteration_number << std::endl;
  std::cout << "Bound= " << bound << std::endl;
  status("Iteration "+i2string(backward_iteration_number)+
         ", bound="+i2string(bound));

  namespacet ns(symbol_table);
  interpolatort interpolator;
  boolbvt solver(interpolator);
  solver.equality_propagation=false;
  
  netlist_bmc_map.map_timeframes(netlist, bound+1, interpolator);

    // build formula
  interpolator.set_partition_id(1);
  build_backward_partition1(interpolator);
  solver.clear_cache();

  interpolator.set_partition_id(2);
  build_backward_partition2(interpolator);
  build_backward_property(interpolator);

    // solver
  fine_timet sat_start_time=current_time();
  decision_proceduret::resultt dec_result=
    solver.dec_solve();
  sat_time += current_time()-sat_start_time;
  switch(dec_result)
  {
    case decision_proceduret::D_SATISFIABLE:
      if(backward_interpolants.empty())
      {
        bmc_mapt bmc_map;
        netlist_bmc_map.build_bmc_map(netlist, bmc_map);
        result("SAT: bug found. Bound=" + i2string(bound));
        result("Iteration " + i2string(forward_iteration_number+backward_iteration_number));
        result("Bound=" + i2string(bound));
        show_counterexample(prop_expr_list, prop_bv, *this, interpolator, bmc_map,
                            ns, ui_message_handlert::PLAIN);
        report_failure();
        std::cout << "returning 0\n";
        return 0;
      }
      else
      {
        status("SAT: interpolation failed, increasing bound, changing property");
        return Refine_Interpolant(solver, interpolator, false);
      }
      break;

    case decision_proceduret::D_UNSATISFIABLE:
    {
      status("UNSAT: getting interpolant, doing widening");
      get_interpolant(interpolator, false);
      backward_fault_locations.clear();
      backward_fault_locations.push_back(0);
      if(reached_fixedpoint(false))
      {
        if(!backward_refinement)
          return 1;
        else
          return 3;
      }
    }
    break;

    case decision_proceduret::D_ERROR:
      std::cout << "Error from decision procedure 5 " << std::endl;
      error("Error from decision procedure");
      return 2;

    default:
      error("Unexpected result from decision procedure");
      return 1;
  }

  return -1;
}

int interpolationt_netlist_vmcai::check_backward_reachable_states()
{
  namespacet ns(symbol_table);
  satcheckt satcheck;
  boolbvt solver(satcheck);
  unsigned check_bound = 2;
  netlist_bmc_mapt netlist_bmc_map_check;
  netlist_bmc_map_check.map_timeframes(netlist, check_bound, satcheck);
  ::unwind(netlist, netlist_bmc_map_check, *this, satcheck, false);

  bmc_mapt bmc_map_check;
  netlist_bmc_map_check.build_bmc_map(netlist, bmc_map_check);
  backward_interpolants.back().aig.add_variables(satcheck); 
  map_to_timeframe(bmc_map_check, backward_interpolants.back().aig, 1);
  literalt l_old_1 = backward_interpolants.back().convert(solver.prop);
  map_from_timeframe(bmc_map_check, backward_interpolants.back().aig, 1);

  literalt l_app_reach = intersect_approx_reachable_states(bmc_map_check, satcheck, false);
  l_old_1 = satcheck.land(l_old_1, l_app_reach);
  satcheck.l_set_to(l_old_1, true);

  bvt all_prop_bv;
  for(unsigned new_iter=0; new_iter < check_bound; new_iter++)
  {
//    literalt l = netlist_bmc_map.translate(new_iter, netlist.initial);
    literalt l_init = const_literal(true);
    for(unsigned i=0; i<netlist.initial.size(); i++)
      l_init = solver.prop.land(netlist_bmc_map.translate(new_iter, netlist.initial.at(i)), l_init);
    all_prop_bv.push_back(l_init);
  }
  literalt l_prop = solver.prop.lor(all_prop_bv);
  satcheck.l_set_to(l_prop, true);
  fine_timet sat_start_time=current_time();
  decision_proceduret::resultt dec_result=
    solver.dec_solve();
  sat_time += current_time()-sat_start_time;
  switch(dec_result)
  {
    case decision_proceduret::D_UNSATISFIABLE:
      result("property holds!");
      result("Iteration " + i2string(forward_iteration_number+backward_iteration_number));
      result("Bound=" + i2string(bound));
      return 3;

    case decision_proceduret::D_SATISFIABLE:
      result("UNSAT: No Result");
      break;

    case decision_proceduret::D_ERROR:
      std::cout << "Error from decision procedure 6 " << std::endl;
      error("Error from decision procedure");
      return 2;

    default:
      error("Unexpected result from decision procedure");
      return 1;
  }
  return -1;
}

void interpolationt_netlist_vmcai::build_backward_property(
  interpolatort &solver)
{
  status("build_property");

  namespacet ns(symbol_table);
  prop_bv.clear();
  
  bvt all_prop_bv;

  prop_bv.push_back(bvt());

  for(unsigned c=0; c<bound; c++)
  {
      //      solver.l_set_to(netlist_bmc_map.translate(c, netlist.initial), true);
//    literalt l_init = netlist_bmc_map.translate(c, netlist.initial);
    literalt l_init = const_literal(true);
    for(unsigned i=0; i<netlist.initial.size(); i++)
      l_init = solver.land(netlist_bmc_map.translate(c, netlist.initial.at(i)), l_init);
    std::cout << "init " << l_init.var_no() << " tf " << c << std::endl;
    prop_bv.back().push_back(l_init);
    all_prop_bv.push_back(l_init);
  }
  prop_bv.back().push_back(const_literal(true));
  solver.l_set_to(solver.lor(all_prop_bv), true);
  status("build_property done");
}


void interpolationt_netlist_vmcai::build_backward_partition1(interpolatort &solver)
{
  status("build_partition1");

  ::unwind(netlist, netlist_bmc_map, *this, solver, false, bound);
  ::unwind(netlist, netlist_bmc_map, *this, solver, false, bound-1);

  namespacet ns(symbol_table);
  bvt all_prop_bv;
  for(unsigned p_no=0; p_no<netlist.properties.size(); p_no++)
  {
    literalt l = netlist_bmc_map.translate(bound, netlist.properties[p_no]);
    std::cout << "prop " << l.var_no() << std::endl;
    all_prop_bv.push_back(l);
  }

  if(backward_interpolants.empty())
  {
    status("property when no interpolant");
    solver.l_set_to(solver.land(all_prop_bv), false);
    status("build_property done");
  }
  else
  {
    status("init with interpolant");
    bvt or_bv;
    bmc_mapt bmc_map_inter;
    netlist_bmc_map.build_bmc_map(netlist, bmc_map_inter);

    literalt l_prop = !solver.land(all_prop_bv);
    or_bv.push_back(l_prop);

    literalt l_prev = union_previous_interpolants(bmc_map_inter, solver, false);
    or_bv.push_back(l_prev);

    std::cout << "mapping to timeframe\n";
    map_to_timeframe(bmc_map_inter, backward_interpolants.back().aig, bound);  //interpolant in timeframe k
    backward_interpolants.back().add_variables(solver);

    literalt l_old_1 = backward_interpolants.back().convert(solver);
    or_bv.push_back(l_old_1);
    map_from_timeframe(bmc_map_inter,backward_interpolants.back().aig, bound); //put it back
    solver.lcnf(or_bv);
  }
}

void interpolationt_netlist_vmcai::build_backward_partition2(
  interpolatort &interp)
{
  status("build_backward_partition2");
    // unwinding for frames 1,..,bound+1
  for(unsigned c=0; c<bound-1; c++)
    ::unwind(netlist, netlist_bmc_map, *this, interp, false, c);
  status("build_backward_partition2 done");
}

void interpolationt_netlist_vmcai::check_if_interpolant_reach_intersect(
  bool forward)
{
  std::vector<aig_formulat> *interpolants = forward ? &forward_interpolants : &backward_interpolants;
  aig_formulat &new_interpolant = interpolants->back();

  satcheckt solver;
  namespacet ns(symbol_table);
  netlist_bmc_mapt netlist_bmc_map_check;
  netlist_bmc_map_check.map_timeframes(netlist, bound+1, solver);

  bmc_mapt bmc_map_inter;
  netlist_bmc_map_check.build_bmc_map(netlist, bmc_map_inter);
  unsigned tf = forward ? 0 : bound;
  map_to_timeframe(bmc_map_inter, new_interpolant.aig, tf);
  new_interpolant.add_variables(solver);

  literalt l_new = new_interpolant.convert(solver);
  map_from_timeframe(bmc_map_inter, new_interpolant.aig, tf); 

  literalt l_app_reach = intersect_approx_reachable_states(bmc_map_inter, solver, forward);
  solver.l_set_to(l_app_reach, true);
  fine_timet sat_start_time=current_time();
  propt::resultt dec_result=
    solver.prop_solve();
  sat_time += current_time()-sat_start_time;
  switch(dec_result)
  {
    case propt::P_SATISFIABLE:
      status("SAT: prev app reach intersect");
      break;
    case propt::P_UNSATISFIABLE:
      result("UNSAT: prev app reach do not.");
        //    assert(0);
      break;
    default:
      throw "unexpected result from SAT-solver";
  }

  l_new = solver.land(l_new, l_app_reach);
  status("converted new interpolant");
  solver.l_set_to(l_new, true);

  sat_start_time=current_time();
  dec_result=
    solver.prop_solve();
  sat_time += current_time()-sat_start_time;
  switch(dec_result)
  {
    case propt::P_SATISFIABLE:
      status("SAT: interpolant and prev app reach intersect");
      break;
    case propt::P_UNSATISFIABLE:
      result("UNSAT: interpolant and prev app reach disjoint.");
        //    assert(0);
      break;
    default:
      throw "unexpected result from SAT-solver";
  }
}
#endif
