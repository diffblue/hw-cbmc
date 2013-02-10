#include <fstream>
#include <stack>
#include <solvers/sat/satcheck.h>

#include "induction_coverage.h"
#include "core.h"
//#include "peripheral.h"
#include "../trans/unwind_netlist.h"
#include "interpolation/bitlevel/normal_resolution_proof.h"


//hide various clauses and check if the proof still exists
void induction_coveraget:: do_coverage()
{

//DONE
    //since the interpolation took k iterations to reach a fixed point,  in the original 
    //system there is no cunterexample of length k.
  log << "Test 2: Incremental counterexample test\n";
  std::cout << "checking CE\n";  
  unsigned bound = original_interpolator.return_bound()+original_interpolator.get_size_of_interpolants()+1;
  log << "Checking if a CE of length " << bound << " exists\n";
  check_ce(bound);
  ce_test.print();
  
  log << "Test 3: Inductive test\n";
    //only use the clauses involved in the proof and check if still inductive
  std::cout  << "Reusing the clauses from proof of inductiveness\n";
  satcheck_minisat_normal_prooft solver_clause;
  induction_resultt is_ind_clause = is_inductive1(false, solver_clause);
  assert(is_ind_clause == INDUCTIVE);
  std::cout << "Original inductive\n";

  satcheckt solver1;
  bmc_mapt netlist_bmc_map_induction;
  netlist_bmc_map_induction.map_timeframes(netlist, 2, solver1); //vars in tf 0 and 1
/*
    //get the core and check it

  check_coret c = check_coret(solver_clause.get_resolution_proof(), 
                              0, netlist, force_selects_node, force_selects_latch);
  c.check_original_core();

  core_test.print();


  remove_not_covered(netlist_bmc_map_induction, 
                     force_selects_latch, 
                     solver_clause);
  remove_not_covered(netlist_bmc_map_induction, 
                     force_selects_node, 
                     solver_clause);


  induction_test.print();
*/  
//DONE
  log << "Test 3: Inductive test Restart\n";  
    //from scratch create an inductive proof and start checking
  satcheck_minisat_normal_prooft solver;
  induction_resultt is_ind = is_inductive(false, solver);
  assert(is_ind == INDUCTIVE);
  std::cout << "Original inductive\n";


  std::cout << "From Scratch\n";
  remove_not_covered_from_scratch(netlist_bmc_map_induction, 
                                  force_selects_latch, 
                                  solver);
  remove_not_covered_from_scratch(netlist_bmc_map_induction, force_selects_node, 
                                  solver);  
  induction_test_from_scratch.print();
  
//DONE  
}



void induction_coveraget::add_clause(const interpolation_resolution_prooft & proof,
                                     satcheckt &new_solver,
                                     std::map< std::string, force_multiplexert> &given_selects_map,
                                     const bmc_mapt &bmc_map)
{
  std::stack<unsigned> s;
  std::vector<bool> seen;

  assert(!proof.r_steps.empty());  
  
  seen.resize(proof.r_steps.size(), false);
  
  s.push(proof.empty_clause_id);

  while(!s.empty())
  {
    unsigned int c_id=s.top();
    s.pop();

    if(seen[c_id]) continue;
    seen[c_id] = true;
    const interpolation_resolution_stept &step = proof.r_steps[c_id];
    if(step.get_is_root())
    {
      const bvt &cl = proof.r_clauses[step.get_res_step_id_1()].root_clause;
      if(cl.size() == 1)
      {
        bool match_found = false;
        for(std::map< std::string, force_multiplexert>::iterator iter = given_selects_map.begin();
            iter != given_selects_map.end(); iter++)
        {
          if(match_found)
            break;
          
          unsigned select = (*iter).second.force_select_var;
          literalt l = bmc_map.translate(0, literalt(select,false));
          if(cl.at(0).var_no() == l.var_no()) // do not add this clause 
            match_found = true;
        }
        if(!match_found)
          new_solver.lcnf(cl);
      }
      else
        new_solver.lcnf(cl);
      
    }
    else
    {
      s.push(step.get_res_step_id_1());
      s.push(step.get_res_step_id_2());
    }
  }
  
}

void induction_coveraget::remove_not_covered(const bmc_mapt &bmc_map,
                                             std::map< std::string, force_multiplexert> &given_selects_map,
                                             satcheck_minisat_normal_prooft &solver)
{
    //traverse the proof..take the roof clause
  fine_timet start_time = current_time();  
  const interpolation_resolution_prooft & proof = solver.get_resolution_proof();
  
  satcheckt new_solver;
  new_solver.set_no_variables(solver.no_variables());
//  new_solver.add_variables();
  add_clause(proof, new_solver, given_selects_map, bmc_map);

  bvt assumptions;  
  get_assumptions_for_timeframe(assumptions, bmc_map, false, 0);  
  get_assumptions_for_timeframe(assumptions, bmc_map, false, 1);  
 
  new_solver.set_assumptions(assumptions);

  propt::resultt dec_result = new_solver.prop_solve();
  assert(dec_result == propt::P_UNSATISFIABLE);
  
  
  for(std::map< std::string, force_multiplexert>::iterator iter = given_selects_map.begin();
      iter != given_selects_map.end(); iter++)
  {
    std::map< std::string, force_multiplexert>::iterator current_iter = iter;

    for(int i= (int) NONDET; i >= (int) ZERO; i--)
    {
      
      if((*current_iter).second.coverage.at(i).result != UNKNOWN) // NOTCOVERED
        continue;

      std::cout << "checking for " << (*current_iter).first << 
        " " << (*current_iter).second.force_select_var << std::endl;
      std::cout << "Forcing to " << i << std::endl;

      force_map.clear();
      unsigned select = (*current_iter).second.force_select_var;
      unsigned val = (*(current_iter)).second.force_val_var;    
      force_map.insert(std::make_pair(select, force_valuet(val, force_typet(i))));
    
      bvt assumptions;  
      get_assumptions_for_timeframe(assumptions, bmc_map, true, 0);  
      new_solver.set_assumptions(assumptions);

      propt::resultt dec_result = new_solver.prop_solve();
      switch(dec_result)  
      {
        case propt::P_SATISFIABLE:
          break;
      
        case propt::P_UNSATISFIABLE:
        {
          status("SAT: inductive..not covered for sure");
          (*current_iter).second.set_coverage(i, NOTCOVERED, INDUCTION);
          induction_test.inductive++;
          if( i == (int) NONDET)
          {
            if((*current_iter).second.coverage.at((int) ONE ).result == UNKNOWN)
            {
              induction_test.nondet_inductive++;
              (*current_iter).second.set_coverage((int) ONE, NOTCOVERED, INDUCTION_SKIP);
            }
            if((*current_iter).second.coverage.at((int) ZERO ).result == UNKNOWN)
            {
              induction_test.nondet_inductive++;
              (*current_iter).second.set_coverage((int) ZERO, NOTCOVERED, INDUCTION_SKIP);
            }
          }
        }
        break;
        default:
          throw "unexpected result from SAT-solver";    
      } 
    }
  }
  induction_test.total_time += current_time() -start_time;
}


void induction_coveraget::check_ce(unsigned bound)
{
  fine_timet start_time = current_time();
  std::cout << "check if a REAL CE of length <= " << bound << " exists\n";  
  satcheckt solver_ce;
  cmdlinet cmdline;
  ebmc_baset ebmc_base(cmdline);
  bmc_mapt bmc_map_ce;
  std::list<bvt> prop_bv;
  bmc_map_ce.map_timeframes(netlist, bound+1, solver_ce); //original_interpolator.get_size_of_interpolants()+2 timeframes
  ::unwind(netlist, bmc_map_ce, *this, solver_ce, true);
  ::unwind_property(netlist, bmc_map_ce, *this, prop_bv, solver_ce);

  bvt assumptions;
  get_assumptions(assumptions, bmc_map_ce, false, bound);
  solver_ce.set_assumptions(assumptions);

  propt::resultt dec_result= solver_ce.prop_solve();
  assert(dec_result == propt::P_UNSATISFIABLE);

  remove_covered(bmc_map_ce, force_selects_latch, solver_ce, prop_bv, bound);
  remove_covered(bmc_map_ce, force_selects_node, solver_ce, prop_bv, bound);  
  ce_test.total_time += current_time() - start_time;
}


//from check_ce
void induction_coveraget::remove_covered(const bmc_mapt &bmc_map,
                                                      std::map< std::string, force_multiplexert> &given_selects_map,
                                                      satcheckt &solver,
                                                      std::list<bvt> &prop_bv1,
                                                      unsigned bound)
{
  for(std::map< std::string, force_multiplexert>::iterator iter = given_selects_map.begin();
      iter != given_selects_map.end(); iter++)
  {
    for(int i= (int) NONDET; i >= (int) ZERO; i--)
    {
      
      if((*iter).second.coverage.at(i).result != UNKNOWN)
        continue;

      std::cout << "checking for " << (*iter).first << 
        " " << (*iter).second.force_select_var << std::endl;
      std::cout << "Forcing to " << i << std::endl;

      fine_timet start_time = current_time();
      force_map.clear();
      unsigned select = (*iter).second.force_select_var;
      unsigned val = (*(iter)).second.force_val_var;    
      force_map.insert(std::make_pair(select, force_valuet(val, force_typet(i))));
    
      bvt assumptions;  
      for(unsigned t=0;  t< bound; t++)
        get_assumptions_for_timeframe(assumptions, bmc_map, true, t);

      solver.set_assumptions(assumptions);
      propt::resultt dec_result = solver.prop_solve();
      namespacet ns(symbol_table);
      
      switch(dec_result)
      {
        case propt::P_SATISFIABLE:
        {          
          ce_test.counterexample++;
          (*iter).second.set_coverage(i, COVERED, CE);

            //check if any test of ZERO or ONE can be skipped
            //collect all the related multiplexors are forced zero
#if 0
          if(i == (int) NONDET)
          {
          
            satcheckt s1;
            bmc_mapt netlist_bmc_map;
            netlist_bmc_map.map_timeframes(netlist, bound+1, s1);

            bool get_val = true;
            bool can_skip = true;

              //get length of the counterexample
            unsigned length;
            for(std::list<bvt>::const_iterator p_it=prop_bv1.begin();
                p_it!=prop_bv1.end();
                p_it++)
            {
              const bvt &bv=*p_it;
              for(unsigned t=0; t<= bound; t++)
              {
                tvt result=solver.l_get(bv[t]);
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
              tvt new_sim = solver.l_get(l);
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
                ce_test.reused_counterexample++;
                (*iter).second.set_coverage(int(get_val), COVERED, CE_SKIP);
              }
            }
          }
          #endif

        }
        break;
        case propt::P_UNSATISFIABLE:
        {
            //nothing to do
          break;
        }
        default:
          throw "unexpected result from SAT-solver";    
      }
    } 
  }
}


void induction_coveraget::remove_not_covered_from_scratch(const bmc_mapt &bmc_map,
                                             std::map< std::string, force_multiplexert> &given_selects_map,
                                             satcheckt &solver)
{
  
  for(std::map< std::string, force_multiplexert>::iterator iter = given_selects_map.begin();
      iter != given_selects_map.end(); iter++)
  {
    std::map< std::string, force_multiplexert>::iterator current_iter = iter;

    for(int i= (int) NONDET; i >= (int) ZERO; i--)
    {
      
      if((*current_iter).second.coverage.at(i).result != UNKNOWN) // NOTCOVERED
        continue;

      std::cout << "checking for " << (*current_iter).first << 
        " " << (*current_iter).second.force_select_var << std::endl;
      std::cout << "Forcing to " << i << std::endl;

      fine_timet start_time = current_time();
      force_map.clear();
      unsigned select = (*current_iter).second.force_select_var;
      unsigned val = (*(current_iter)).second.force_val_var;    
      force_map.insert(std::make_pair(select, force_valuet(val, force_typet(i))));
    
      bvt assumptions;  
      get_assumptions_for_timeframe(assumptions, bmc_map, true, 0);  
      solver.set_assumptions(assumptions);

      induction_test_from_scratch.total_tests++;
      propt::resultt dec_result = solver.prop_solve();
      
      namespacet ns(symbol_table);
      
      switch(dec_result)
      {
        case propt::P_SATISFIABLE:
          std::cout << "SAT: not inductive..don't know coverage" << std::endl;
          induction_test_from_scratch.non_inductive++;
//          show_counterexample(*this, solver, bmc_map,
//                          ns, ui_message_handlert::PLAIN);

//the selected clauses do no give rise to UNSAT.
            //but there may exist another one
          break;
        case propt::P_UNSATISFIABLE:
          std::cout << "SAT: inductive..not covered for sure" << std::endl;
          (*current_iter).second.set_coverage(i, NOTCOVERED, INDUCTION_SCRATCH);
          induction_test_from_scratch.inductive++;
          if(i  == (int) NONDET)
          {
//            std::cout << "in NONDET\n";
            
            (*current_iter).second.set_coverage((int) ONE, NOTCOVERED, INDUCTION_SCRATCH_SKIP);
            (*current_iter).second.set_coverage((int) ZERO, NOTCOVERED, INDUCTION_SCRATCH_SKIP);
            induction_test_from_scratch.nondet_inductive++;
            induction_test_from_scratch.nondet_inductive++;
          }
//          std::cout << induction_test_from_scratch.nondet_inductive << std::endl;
//          std::cout << induction_test_from_scratch.inductive << std::endl;
          break;
        default:
          throw "unexpected result from SAT-solver";    
      }
      induction_test_from_scratch.total_time += current_time()-start_time;
    }
  }
}


#if 0
void induction_coveraget::remove_not_covered_test_from_scratch(const bmc_mapt &bmc_map,
                                                               std::map< std::string, force_multiplexert> &given_selects_map)
{
  
  for(std::map< std::string, force_multiplexert>::iterator iter = given_selects_map.begin();
      iter != given_selects_map.end(); )
  {
    std::map< std::string, force_multiplexert>::iterator current_iter = iter;
    iter++;
    for(int i = (int) NONDET; i >= (int) ZERO; i--)
    {
      if((*current_iter).second.coverage.at(i).result != UNKNOWN) // NOTCOVERED
        continue;
      
      std::cout << "checking for " << (*current_iter).first << 
        " " << (*current_iter).second.force_select_var << std::endl;
      std::cout << "Forcing to " << i << std::endl;

      fine_timet start_time = current_time();
      
      force_map.clear();
      unsigned select = (*current_iter).second.force_select_var;
      unsigned val = (*current_iter).second.force_val_var;
  
      force_map.insert(std::make_pair(select, force_valuet(val, force_typet(i))));
//      std::cout << "from scratch :: checking for inductiveness " << select << " " << val << std::endl;
      satcheckt solver;
      induction_test_from_scratch.total_tests++;
      induction_resultt res = is_inductive(true, solver);
      if(res == INDUCTIVE)
      {
//        std::cout << "ERASING " << i << std::endl;
        (*current_iter).second.set_coverage(i, NOTCOVERED, INDUCTION_SCRATCH);
        induction_test_from_scratch.inductive++;
        if( i == (int) NONDET)
        {
          if((*current_iter).second.coverage.at((int) ONE ).result == UNKNOWN)
          {
            induction_test_from_scratch.nondet_inductive++;
            (*current_iter).second.set_coverage((int) ONE, NOTCOVERED, INDUCTION_SCRATCH);
          }
          if((*current_iter).second.coverage.at((int) ZERO ).result == UNKNOWN)
          {
            induction_test_from_scratch.nondet_inductive++;
            (*current_iter).second.set_coverage((int) ZERO, NOTCOVERED, INDUCTION_SCRATCH);
          }
        }

      }
      else 
      {
        if (res == REALCE)
        {
          induction_test_from_scratch.counterexample++;  
///*          
          if(i == (int) NONDET)
          {
            satcheckt s1;
            bmc_mapt netlist_bmc_map;
            netlist_bmc_map.map_timeframes(netlist, 1, s1);

              //we may be able to skip ZERO or ONE test depending on the force val
            literalt l = netlist_bmc_map.translate(0, literalt(val,false));
            tvt new_sim = solver.l_get(l);
            if(new_sim.is_known())
            {
              if(new_sim.is_true())
              {
                if((*current_iter).second.coverage.at((int) ONE ).result == UNKNOWN)
                {                
//                  std::cout << "from scratch:: 1 is also covered\n";
                  (*current_iter).second.set_coverage(1, COVERED, INDUCTION_SCRATCH_SKIP);
                  induction_test_from_scratch.reused_counterexample++;  
                }
              }        
              else
              {
                if((*current_iter).second.coverage.at((int) ZERO).result == UNKNOWN)
                {  
//                  std::cout << "from scratch:: 0 is also covered\n";
                  (*current_iter).second.set_coverage(0, COVERED, INDUCTION_SCRATCH_SKIP);
                  induction_test_from_scratch.reused_counterexample++;  
                }
              }
            }
            else
            {
              if((*current_iter).second.coverage.at((int) ONE ).result == UNKNOWN)
              {
//                std::cout << "unknown val from scratch:: 1 is also covered\n";
                (*current_iter).second.set_coverage(1, COVERED, INDUCTION_SCRATCH_SKIP);
                induction_test_from_scratch.reused_counterexample++;  
              }
              if((*current_iter).second.coverage.at((int) ZERO).result == UNKNOWN)
              {  
//                std::cout << "unknown from scratch:: 0 is also covered\n";
                (*current_iter).second.set_coverage(0, COVERED, INDUCTION_SCRATCH_SKIP);
                induction_test_from_scratch.reused_counterexample++;  
              }
            }
          }
//*/
          (*current_iter).second.set_coverage(i, COVERED, INDUCTION_SCRATCH);
        }
        else
          induction_test_from_scratch.non_inductive++;  
      }
      induction_test_from_scratch.total_time += current_time()-start_time;
    }
  }
  
}
#endif
induction_resultt induction_coveraget::is_inductive(bool force,
                                                    satcheckt &interpolator,
                                                    bool assume)
{
  namespacet ns(symbol_table);

  bmc_mapt netlist_bmc_map_induction;
  netlist_bmc_map_induction.map_timeframes(netlist, 2, interpolator); //vars in tf 0 and 1
  literalt l_unwinding = unwind(interpolator, netlist_bmc_map_induction, 0, true, true);
  interpolator.l_set_to(l_unwinding, true);
  literalt l_init = unwind(interpolator, netlist_bmc_map_induction, 1, true, false);
  interpolator.l_set_to(l_init, false);

  bvt assumptions;  
  get_assumptions(assumptions, netlist_bmc_map_induction, force, 0);

  if(assume)
    interpolator.set_assumptions(assumptions);
  else
  {  
    for(unsigned i=0; i < assumptions.size(); i++)
    {
      interpolator.l_set_to(assumptions.at(i), true);
    }
  }
  
  
  propt::resultt dec_result = interpolator.prop_solve();
  switch(dec_result)  
  {
    case propt::P_SATISFIABLE:
    {
      status("SAT: not inductive..don't know coverage");
        //check if its a real counterexample.
        //by adding init(0)
//      show_counterexample(*this, interpolator, netlist_bmc_map_induction,
//                          ns, ui_message_handlert::PLAIN);

      ::unwind(netlist, netlist_bmc_map_induction, *this, interpolator, true);

      std::list<bvt> prop_bv2;
      ::unwind_property(netlist, netlist_bmc_map_induction, *this, prop_bv2, interpolator);
      
      propt::resultt dec_result1 = interpolator.prop_solve();      
      interpolator.set_assumptions(assumptions);
      if(dec_result1 == propt::P_SATISFIABLE)
      {
//      show_counterexample(*this, interpolator, netlist_bmc_map_induction,
//                          ns, ui_message_handlert::PLAIN);

        return REALCE;
      }
      return NOTINDUCTIVE;
    }
    case propt::P_UNSATISFIABLE:
      status("SAT: inductive..not covered for sure");
      return INDUCTIVE;
    default:
      throw "unexpected result from SAT-solver";    
  }
}

literalt induction_coveraget::unwind(
  cnft &solver,
  const bmc_mapt &bmc_map,
  unsigned t,
  bool initial_states,
  bool transition)
{
  literalt l_unwinding = const_literal(true);
  if(initial_states)
  {
    for(unsigned i=0; i<netlist.initial.size(); i++)
      l_unwinding = solver.land(
        bmc_map.translate(t, netlist.initial[i]), l_unwinding);

    literalt l_approx = const_literal(false);
    for(unsigned i=0; i < original_interpolator.get_size_of_interpolants(); i++)
    {
      bmc_mapt last_map;
      literalt l_old = (original_interpolator.get_interpolant(i)).instantiate(last_map, bmc_map, solver, t);
      l_approx = solver.lor(l_old, l_approx);
    }

    l_unwinding = solver.lor(l_unwinding, l_approx);
  }
  
  if(!transition)
    return l_unwinding;
  
  const bmc_mapt::timeframet &timeframe=bmc_map.timeframe_map[t];
  
  for(unsigned n=0; n<timeframe.size(); n++)
  {
    const aig_nodet &node=netlist.get_node(n);

    if(node.is_and() && timeframe[n].is_visible)
    {
      literalt la=bmc_map.translate(t, node.a);
      literalt lb=bmc_map.translate(t, node.b);
      
      solver.gate_and(la, lb, timeframe[n].solver_literal);
    }
  }

  // transition constraints
  for(unsigned i=0; i<netlist.transition.size(); i++)
    l_unwinding = solver.land(
      bmc_map.translate(t, netlist.transition[i]), l_unwinding);

    // joining the latches between timeframe and timeframe+1
    for(var_mapt::mapt::const_iterator
        v_it=netlist.var_map.map.begin();
        v_it!=netlist.var_map.map.end();
        v_it++)
    {
      const var_mapt::vart &var=v_it->second;
      if(var.is_latch())
      {
        for(unsigned bit_nr=0; bit_nr<var.bits.size(); bit_nr++)
        {
          const var_mapt::vart::bitt &bit=var.bits[bit_nr];
          
          literalt l_from=bit.next;
          literalt l_to=bit.current;

          if(l_from.is_constant() ||
             bmc_map.timeframe_map[t][l_from.var_no()].is_visible)
            solver.set_equal(
              bmc_map.translate(t, l_from),
              bmc_map.translate(t+1, l_to));
        }
      }
    }
  
  return l_unwinding;
}

induction_resultt induction_coveraget::is_inductive1(bool force,
                                                    satcheck_minisat_normal_prooft &interpolator)
{
  namespacet ns(symbol_table);

  interpolator.set_partition_id(1);
  bmc_mapt netlist_bmc_map_induction;
  netlist_bmc_map_induction.map_timeframes(netlist, 2, interpolator); //vars in tf 0 and 1
  literalt l_unwinding = unwind(interpolator, netlist_bmc_map_induction, 0, true, true);
  interpolator.l_set_to(l_unwinding, true);
  literalt l_init = unwind(interpolator, netlist_bmc_map_induction, 1, true, false);
  interpolator.l_set_to(l_init, false);

  interpolator.set_partition_id(2);
  bvt assumptions;  
  get_assumptions(assumptions, netlist_bmc_map_induction, force, 0);

  for(unsigned i=0; i < assumptions.size(); i++)
  {
    interpolator.l_set_to(assumptions.at(i), true);
  }

  propt::resultt dec_result = interpolator.prop_solve();
  switch(dec_result)  
  {
    case propt::P_SATISFIABLE:
    {
      status("SAT: not inductive..don't know coverage");
        //check if its a real counterexample.
        //by adding init(0)
//      show_counterexample(*this, interpolator, netlist_bmc_map_induction,
//                          ns, ui_message_handlert::PLAIN);

      ::unwind(netlist, netlist_bmc_map_induction, *this, interpolator, true);

      std::list<bvt> prop_bv2;
      ::unwind_property(netlist, netlist_bmc_map_induction, *this, prop_bv2, interpolator);
      
      propt::resultt dec_result1 = interpolator.prop_solve();      
      interpolator.set_assumptions(assumptions);
      if(dec_result1 == propt::P_SATISFIABLE)
      {
//      show_counterexample(*this, interpolator, netlist_bmc_map_induction,
//                          ns, ui_message_handlert::PLAIN);

        return REALCE;
      }
      return NOTINDUCTIVE;
    }
    case propt::P_UNSATISFIABLE:
      status("SAT: inductive..not covered for sure");
      return INDUCTIVE;
    default:
      throw "unexpected result from SAT-solver";    
  }
}
