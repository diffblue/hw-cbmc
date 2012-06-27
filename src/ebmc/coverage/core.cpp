#include "core.h"

void check_coret::check_original_core()
{
  fine_timet start_time = current_time();
  original_proof.build_core(core);

  bmc_mapt check_map;
  satcheck_minisat_normal_prooft interpolator;
//  int bound = original_interpolator.return_bound();
  check_map.map_timeframes(working_netlist, bound+1, interpolator);

  std::cout << "Bound is " << bound << std::endl;
  
  remove_notcovered(force_selects_latch, check_map);
  remove_notcovered(force_selects_node, check_map);
  
  core_test.total_time += current_time() - start_time;
}

void check_coret::remove_notcovered(std::map< std::string, force_multiplexert> &given_map,
                                    const bmc_mapt &check_map)
{
   
  for(std::map< std::string, force_multiplexert>::iterator iter = given_map.begin();
      iter != given_map.end(); iter++)
  {
    if(((*iter).second.coverage.at(int (ZERO)).result == UNKNOWN) ||
       ((*iter).second.coverage.at(int (ONE)).result == UNKNOWN) ||
       ((*iter).second.coverage.at(int (NONDET)).result == UNKNOWN))
    {
      bool in_core = false;
      
      for(unsigned c=0; c<bound+1; c++) //note the difference here
      {
        literalt l = check_map.translate(c, literalt((*iter).second.force_select_var, 
                                                     false));
//        std::cout << "checking " << l.dimacs() << std::endl;
        
        assert(!l.sign());
        if(core[l.var_no()])
        {
          in_core = true;
//          std::cout << "in core " << l.dimacs() << std::endl;
          if(remove)
            break;
        }
      }
      if(!in_core)
      {
//        std::cout << "Removing " << (*iter).first << std::endl;
//        std::cout << "Removing " << core_test.not_covered << std::endl;
        core_test.not_covered = core_test.not_covered + 3;
//        std::cout << "Removing " << core_test.not_covered << std::endl;
        if(remove)
        {
          (*iter).second.set_coverage(2, NOTCOVERED, CORE);
          (*iter).second.set_coverage(1, NOTCOVERED, CORE);
          (*iter).second.set_coverage(0, NOTCOVERED, CORE);
        }
      }
    } 
  }
}

