#include <fstream>
#include <algorithm>
#include "interpolation_coverage.h"
#include "core.h"

void interpolation_coveraget::do_coverage()
{
  log << "Test 4: Interpolation Test\n";
  fixed_bound = bound;
  fine_timet start_time = current_time();  
  remove_not_covered(force_selects_latch);
  remove_not_covered(force_selects_node);
  interpolation_test.total_time = current_time() - start_time;
  interpolation_test.print();
}

void interpolation_coveraget::remove_not_covered(
  std::map<std::string, force_multiplexert> &given_map)
{
  
  for(std::map< std::string, force_multiplexert>::iterator iter = given_map.begin();
      iter != given_map.end(); iter++)
  {
    unsigned select = (*iter).second.force_select_var;
//      unsigned val = (*(force_vals_latch.find((*iter).first))).second;
    unsigned val = (*iter).second.force_val_var;
  
    for(int i= (int) NONDET; i >= (int) ZERO; i--)
    {

      if((*iter).second.coverage.at(i).result != UNKNOWN) // NOTCOVERED 
        continue;

      fine_timet start_time = current_time();
      interpolation_test.total_tests++;
      
      force_map.clear();
      force_map.insert(std::make_pair(select, force_valuet(val, force_typet(i))));
      std::cout << "checking for " << (*iter).first << " " << (*iter).second.force_select_var << std::endl;
      std::cout << "Forcing to " << i << std::endl;

      bound = fixed_bound;
      std::cout << "fixed_bound is " << fixed_bound << std::endl;
      
      int result = do_interpolation();
      if(result == 1)   //fixed point
      {  
        interpolation_test.fixedpoint++;
        (*iter).second.set_coverage(i, NOTCOVERED, INTERPOLATION);
        if( i == (int) NONDET)
        {  
          if((*iter).second.coverage.at((int) ONE ).result == UNKNOWN)
          {
            interpolation_test.nondet_fixedpoint++;
            (*iter).second.set_coverage((int) ONE, NOTCOVERED, INTERPOLATION);
          }
          if((*iter).second.coverage.at((int) ZERO ).result == UNKNOWN)
          { 
            interpolation_test.nondet_fixedpoint++;
            (*iter).second.set_coverage((int) ZERO, NOTCOVERED, INTERPOLATION);
          }
        }
      }
      else if(result == 0)
      {
        interpolation_test.counterexample++;
        (*iter).second.set_coverage(i, COVERED, INTERPOLATION);
          //check if any test of ZERO or ONE can be skipped
          //collect all the related multiplexors are forced zero
        if(i == (int) NONDET)
        {
          
          interpolatort s1;
          bmc_mapt netlist_bmc_map;
          netlist_bmc_map.map_timeframes(working_netlist, bound+1, s1);

          bool get_val = true;
          bool can_skip = true;

            //get length of the counterexample
          unsigned length;
          for(std::list<bvt>::const_iterator p_it=prop_bv.begin();
              p_it!=prop_bv.end();
              p_it++)
          {
            const bvt &bv=*p_it;
            for(unsigned t=0; t<= bound; t++)
            {
              tvt result=final_decision_interpolator.l_get(bv[t]);

              if(result.is_false())
              {
                length = t;
                break;
              }
            }
          }
        
          for(unsigned c=0; c < length; c++) //for latches
          {
            literalt l = netlist_bmc_map.translate(c, literalt(val,false));
            tvt new_sim = final_decision_interpolator.l_get(l);
            std::string v = new_sim.is_known() ? new_sim.is_true() ? "1" : "0" : "X";
            if(new_sim.is_known()) {
              {
                if(c == 0)
                  get_val = new_sim.is_true();
                else if(get_val != new_sim.is_true())
                {
                    //can not skip
                can_skip = false;
                break;
                }
              }
            }
          }
          if(can_skip)
          {
            if((*iter).second.coverage.at((int) get_val).result == UNKNOWN)
            {
              interpolation_test.reused_counterexample++;
              (*iter).second.set_coverage(int(get_val), COVERED, INTERPOLATION_SKIP);
            }
          }
        }
      }
    }
  }
}


int interpolation_coveraget::do_interpolation()
{
  fine_timet start_time =current_time();
  
    // check the initial state
  int result=-1;
  {
      // now do main loop
    iteration_number=0;
    do result=iteration(); while(result==-1);
  }

  std::cout << "Total time = " << time2string(current_time()-start_time) << std::endl;
  std::cout << "SAT time = " << time2string(sat_time) << std::endl;
  
  std::cout << "Fixed point time = " << time2string(fix_check_time) << std::endl;
  std::cout << "Minimization time = " << time2string(minimization_time) << std::endl;
  return result;
}

/*
  returns 
-1 for result not yet found
0 if Bug
1 if fixed point reached
2 : error
3: default
*/
int interpolation_coveraget::iteration()
{
  iteration_number++;

  std::cout << "Iteration " << iteration_number << std::endl;
  std::cout << "Bound= " << bound << std::endl;
  status("Iteration "+i2string(iteration_number)+
         ", bound="+i2string(bound));

  namespacet ns(context);
  interpolatort interpolator;
  boolbvt solver(ns, interpolator);
  solver.equality_propagation=false;
  bmc_mapt netlist_bmc_map;

  netlist_bmc_map.map_timeframes(working_netlist, bound+1, interpolator);
//  netlist_bmc_map.print();
  
  interpolator.set_partition_id(1);
  build_partition1(interpolator, netlist_bmc_map);
  solver.clear_cache();

  interpolator.set_partition_id(3);
  build_partition2(interpolator, netlist_bmc_map);
  build_property(interpolator, netlist_bmc_map);

  interpolator.set_partition_id(2);
  bvt assumptions_1;
  get_assumptions_for_timeframe(assumptions_1, netlist_bmc_map, true, 0);
  for(unsigned i=0; i < assumptions_1.size(); i ++)
    interpolator.l_set_to(assumptions_1.at(i), true);

  interpolator.set_partition_id(4);
    //set assumptions
  bvt assumptions_2;
  for(unsigned i=1;  i< bound+1; i++)
    get_assumptions_for_timeframe(assumptions_2, netlist_bmc_map, true, i);
  for(unsigned i=0; i < assumptions_2.size(); i ++)
    interpolator.l_set_to(assumptions_2.at(i), true);
  
//  interpolator.set_assumptions(assumptions);
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
//        show_counterexample(prop_expr_list, prop_bv, *this, interpolator, netlist_bmc_map,
//                            ns, ui_message_handlert::PLAIN);
        final_decision_interpolator.swap_solver(interpolator);
        report_failure();
        return 0;
      }
      else
      {
        bound++;
        forward_interpolants.clear();
      }
      break;

    case decision_proceduret::D_UNSATISFIABLE:
      status("UNSAT: getting interpolant, doing widening");
      {
//        get_interpolant(interpolator, netlist_bmc_map);
        std::set<unsigned> s1;
        s1.insert(1);
        s1.insert(2);
        
        do_interpolationt do_interpolation(s1, interpolator.get_resolution_proof());
        bit_interpolantt inter_ken = do_interpolation.get_interpolant();
        if(inter_ken.is_true() || inter_ken.is_false())
        forward_interpolants.push_back(inter_ken);
else
{
        bit_interpolantt inter_netlist = inter_ken.map_from_timeframe(netlist_bmc_map, 1);
#if DEBUG
        if(!check_partition_one_implies_interpolant(inter_netlist) ||
           !check_partition_two_and_interpolant(inter_netlist))
        {
          std::cout << "KEN NOT CORRECT\n";
          assert(0);
        }
#endif
        forward_interpolants.push_back(inter_netlist);
}
#if 0
        const char *red_name = "bound_proof";
        std::vector<bool> skeleton_vars(interpolator.get_resolution_proof().no_vars+1, false);
        std::ofstream red(red_name, std::ios::out);
        interpolator.get_resolution_proof().print_proof_in_dot(
          interpolator.get_resolution_proof().empty_clause_id,
          red, skeleton_vars);
        red.close();

        std::cout << "Computing latches\n";

        std::set<unsigned> s;
        s.insert(1);//2
        s.insert(3);//4
        
        do_interpolationt do_interpolationP(s,interpolator.get_resolution_proof());
        bit_interpolantt inter_latch = do_interpolationP.get_interpolant();
 
        std::cout << inter_latch << std::endl;

        check_coret c = check_coret(interpolator.get_resolution_proof(), 
                                    bound, working_netlist, force_selects_node, force_selects_latch);
        c.remove = false;
        c.check_original_core();
        getchar();
#endif
        
        if(reached_fixedpoint())
        {
//          resolution_proof = interpolator.get_resolution_proof();
          final_decision_interpolator.swap_proof(interpolator);
          result("Property holds. Bound="+ i2string(bound));
//          std::cout << "fixed point time " << time2string(fix_check_time) << std::endl; 
          return 1;
        }

      
          //see if induction succeeds
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




int interpolation_coveraget::induction_step()
{
  status("Induction Step");
  
  namespacet ns(context);
  interpolatort satcheck;
  boolbvt solver(ns, satcheck);
  
  bmc_mapt netlist_bmc_map_induction;
  netlist_bmc_map_induction.map_timeframes(working_netlist, bound+1, satcheck);

    // *no* initial state
  status("instantiating trans");
  ::unwind(working_netlist, netlist_bmc_map_induction, *this, satcheck, 0);
  build_partition2(satcheck, netlist_bmc_map_induction);

  bvt assumptions;  
  get_assumptions(assumptions, netlist_bmc_map_induction, true, bound);  
  satcheck.set_assumptions(assumptions);

  unsigned no_timeframes=bound+1;

  for(unsigned p=0; p<working_netlist.properties.size(); p++)
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
      result("UNSAT: inductive proof successful.Bound="+ i2string(bound));
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

bool interpolation_coveraget::check_partition_one_implies_interpolant(const bit_interpolantt &current_inter)
{
  namespacet ns(context);
  interpolatort interpolator;
  boolbvt solver(ns, interpolator);
 
  bmc_mapt bmc_map_temp;
  bmc_map_temp.map_timeframes(working_netlist, bound+1, interpolator);

  build_partition1(interpolator, bmc_map_temp);

  bmc_mapt last_map;
  literalt l_current = current_inter.instantiate(last_map, bmc_map_temp, interpolator, 1);

  interpolator.l_set_to(l_current, false);

  bvt assumptions;  
  get_assumptions(assumptions, bmc_map_temp, true, bound);  
  interpolator.set_assumptions(assumptions);

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



bool interpolation_coveraget::check_partition_two_and_interpolant(const bit_interpolantt &current_inter)
{
  namespacet ns(context);
  interpolatort interpolator;
  boolbvt solver(ns, interpolator);

  bmc_mapt bmc_map_temp;
  bmc_map_temp.map_timeframes(working_netlist, bound+1, interpolator);

  build_partition2(interpolator, bmc_map_temp);
  build_property(interpolator, bmc_map_temp);

  bmc_mapt last_map;
  literalt l_current = current_inter.instantiate(last_map, bmc_map_temp, interpolator, 1);

  interpolator.l_set_to(l_current, true);
  bvt assumptions;  
  get_assumptions(assumptions, bmc_map_temp, true, bound);  
  interpolator.set_assumptions(assumptions);

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

void interpolation_coveraget::check_invariant()
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

  bvt assumptions;  
  get_assumptions(assumptions, bmc_map, false,0);  
  solver.set_assumptions(assumptions);


  propt::resultt dec_result = solver.prop_solve();
  namespacet ns(context);
  
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

