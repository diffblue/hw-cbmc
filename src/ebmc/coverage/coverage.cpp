#include <fstream>
#include "coverage.h"
#include "interpolation_coverage.h"
#include "induction_coverage.h"
#include "core.h"
//#include "peripheral.h"
/*******************************************************************\

Function: do_coverage_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/


unsigned coveraget::make_new_var_node(const irep_idt &name)
{
  working_netlist.new_var_node();
  unsigned var_no = working_netlist.number_of_nodes()-1;
  
    //put the position in vart
  var_mapt::vart v;
  v.bits.resize(1);
  var_mapt::vart::bitt b;
  b.current = literalt(var_no, false);
  b.next = literalt(var_no, false);
  v.bits.at(0) = b;
  v.vartype = var_mapt::vart::VAR_INPUT;
  v.type = typet("bool");
  
    //add in reverse_map, get back the position
  working_netlist.var_map.add(name, 0, v);

    //put the vart in map
  working_netlist.var_map.map.insert(std::make_pair(name, v));
  return var_no;
}


void coveraget::introduce_multiplexor_for_latch(var_mapt::vart &var,
                                                irep_idt name,
                                                unsigned i)
{
    //need to change the next state function
  literalt orig_lit = var.bits[i].next;
      
    //select node
  irep_idt var_name = id2string(name) + "[" + i2string(i)+ "]";
  irep_idt force_name =  id2string(var_name) + "Selforce";
  
  unsigned p = make_new_var_node(force_name);
  literalt force_lit = literalt(
    working_netlist.number_of_nodes()-1, false); //+ve

  force_multiplexert fmt;
  fmt.force_select_var = working_netlist.number_of_nodes()-1; //p
  force_selects_latch[id2string(var_name)] = fmt;
  
  working_netlist.new_and_node(orig_lit, force_lit.negation()); 
  literalt and1 = literalt(working_netlist.number_of_nodes()-1, false); //+ve
  irep_idt force_val_name = id2string(var_name) + "Valforce";
  unsigned p1 = make_new_var_node(force_val_name);
  literalt force_val_lit = literalt(
    working_netlist.number_of_nodes()-1, false); //+ve
  force_selects_latch[id2string(var_name)].force_val_var = working_netlist.number_of_nodes()-1;//p1;

    //force node
  working_netlist.new_and_node(force_val_lit, force_lit);
  literalt and2 = literalt(working_netlist.number_of_nodes()-1, false); //+ve

  working_netlist.new_and_node(and1.negation(), and2.negation());
  literalt final_and = literalt(working_netlist.number_of_nodes()-1, true); //-ve
  
  var.bits[i].next = final_and;
}

void coveraget::introduce_multiplexor(unsigned n)
{
//  const netlistt &netlist = original_interpolator.get_netlist();
  
//  return;
  
    const aig_nodet &node=original_netlist.get_node(n);
    if(node.is_and())
    {
      std::cout << n << " and node\n";
      literalt la = node.a;
      literalt lb = node.b;

        //orig node
      working_netlist.new_and_node(la, lb);
      literalt orig_lit = literalt(working_netlist.number_of_nodes()-1, false); //+ve

      irep_idt force_name = i2string(n) + "Selforce";
        //select node
      unsigned p = make_new_var_node(force_name);
      literalt force_lit = literalt(
        working_netlist.number_of_nodes()-1, false); //+ve
      force_multiplexert fmt;
      fmt.force_select_var = working_netlist.number_of_nodes()-1;
      force_selects_node[i2string(n)] = fmt;

      working_netlist.new_and_node(orig_lit, force_lit.negation()); 
      literalt and1 = literalt(working_netlist.number_of_nodes()-1, false); //+ve

      irep_idt force_val_name = i2string(n) + "Valforce";
      unsigned p1= make_new_var_node(force_val_name);
      force_selects_node[i2string(n)].force_val_var = working_netlist.number_of_nodes()-1;//p1;

      literalt force_val_lit = literalt(
        working_netlist.number_of_nodes()-1, false); //+ve

        //force node
      working_netlist.new_and_node(force_val_lit, force_lit);
      literalt and2 = literalt(working_netlist.number_of_nodes()-1, false); //+ve


      working_netlist.new_and_node(and1.negation(), and2.negation());
      literalt final_andnode_lit = literalt(working_netlist.number_of_nodes()-1, false); //+ve

      working_netlist.nodes[n].a = final_andnode_lit.negation();
      working_netlist.nodes[n].b = final_andnode_lit.negation();

    }
}

void coveraget::make_new_netlist()
{
  working_netlist.var_map = original_netlist.var_map;
  
  for(unsigned n=0; n < original_netlist.number_of_nodes(); n++)
  {
    const aig_nodet &node=original_netlist.get_node(n);
    if(node.is_and())
    {
      literalt la= node.a;
      literalt lb = node.b;      
      working_netlist.new_and_node(la,lb);
    }
    else
      working_netlist.new_var_node();
  }
  
  working_netlist.initial = original_netlist.initial;
  working_netlist.transition = original_netlist.transition;  
  working_netlist.properties = original_netlist.properties;  

}

int coveraget :: measure_coverage_naive()
{
  int result = get_model();
  make_netlist(original_netlist);
  make_new_netlist();
  get_bound();
  
  for(var_mapt::mapt::iterator
      it=working_netlist.var_map.map.begin();
      it!=working_netlist.var_map.map.end(); it++)
  {  
    var_mapt::vart &var=it->second;
    for(unsigned i=0; i<var.bits.size(); i++)
      if(var.vartype == var_mapt::vart::VAR_LATCH)
        introduce_multiplexor_for_latch(var, it->first, i);
  }
  
    std::map<std::string, force_multiplexert> given_map = force_selects_latch;
    for(std::map< std::string, force_multiplexert>::iterator iter = given_map.begin();
        iter != given_map.end(); iter++)
    {
      unsigned select = (*iter).second.force_select_var;
      unsigned val = (*iter).second.force_val_var;
  
      for(int i= (int) NONDET; i >= (int) NONDET; i--)
      {
        if((*iter).second.coverage.at(i).result != UNKNOWN) // NOTCOVERED 
          continue;

        interpolationt_netlist dummy(cmdline);
  	std::cout <<"setting bound " << this->bound << std::endl;
	dummy.set_bound(this->bound);
        interpolation_coveraget ict(cmdline, working_netlist, force_selects_node,
                                    force_selects_latch, dummy);

        fine_timet start_time = current_time();
        naive_test.total_tests++;
      
        std::map<unsigned, force_valuet > force_map;
        ict.force_map.insert(std::make_pair(select, force_valuet(val, force_typet(i))));
        std::cout << "checking for " << (*iter).first << " " << (*iter).second.force_select_var << std::endl;
        std::cout << "Forcing to " << i << std::endl;

//            bound = fixed_bound;
//            std::cout << "fixed_bound is " << fixed_bound << std::endl;
      
        int result = ict.do_interpolation();
        if(result == 1)   //fixed point
        {  
          naive_test.fixedpoint++;
          (*iter).second.set_coverage(i, NOTCOVERED, INTERPOLATION);
          if( i == (int) NONDET)
          {  
            if((*iter).second.coverage.at((int) ONE ).result == UNKNOWN)
            {
              naive_test.nondet_fixedpoint++;
              (*iter).second.set_coverage((int) ONE, NOTCOVERED, INTERPOLATION);
            }
            if((*iter).second.coverage.at((int) ZERO ).result == UNKNOWN)
            { 
              naive_test.nondet_fixedpoint++;
              (*iter).second.set_coverage((int) ZERO, NOTCOVERED, INTERPOLATION);
            }
          }
        }
        else if(result == 0)
        {
          naive_test.counterexample++;
          (*iter).second.set_coverage(i, COVERED, INTERPOLATION);
        }
        naive_test.total_time += current_time() - start_time;
      }
    }
    log_naive << "Total number of latches = " << force_selects_latch.size() << std::endl;
    naive_test.print();
    return 1;
}

  

int coveraget :: measure_coverage()
{

  if(cmdline.isset("naive"))
    return measure_coverage_naive();
  
  int result = get_model();
  make_netlist(original_netlist);  
 
  //std::cout << original_netlist << std::endl; 
  original_netlist.output_dot(std::cout);
//  original_netlist.print(std::cout);
//  getchar();
  make_new_netlist();
  get_bound();
  
  
    //change the netlist to add the multiplexor
    // select = 0, original value
    //select = 1, forced value
    //forced value set through assumptions
  
  for(var_mapt::mapt::iterator
      it=working_netlist.var_map.map.begin();
      it!=working_netlist.var_map.map.end(); it++)
  {
    var_mapt::vart &var=it->second;
    for(unsigned i=0; i<var.bits.size(); i++)
      if(var.vartype == var_mapt::vart::VAR_LATCH)
        introduce_multiplexor_for_latch(var, it->first, i);
  }
  
  //change nodes. add multiplexors
  std::cout << "total nodes " << original_netlist.number_of_nodes() << std::endl;
  for(unsigned i=0; i < original_netlist.properties.size(); i++)
  std::cout << "property nodes from " << original_netlist.properties.at(i).var_no() << std::endl;
getchar();

  //for(unsigned n=0; n < original_netlist.number_of_nodes(); n++)
  for(unsigned n=0; n < original_netlist.properties.at(0).var_no(); n++)
  {
    std::cout << "n is " << n << std::endl;
    introduce_multiplexor(n);
  }

  
    //by this time we have received selects and vals 
    //which need to be assumed. and solved

  log << "Started Coverage Analysis\n";
  std::cout << "Check Original design\n";
  
    //let us do model checking on the original exmaple
  fine_timet start_time = current_time();
  
  interpolationt_netlist dummy1(cmdline);
  dummy1.set_unrolling_type(KEN); //Ken
  dummy1.set_minimize(false);
  dummy1.set_induction(false);
  int result_dummy1 = dummy1.do_interpolation();
  if(result_dummy1 == 0)
  {
    log << "Original formula failed\n";
    return 0;
  }
  
  assert(result_dummy1 == 1);  
  log << "Passing Property\n";
  
  fine_timet time_orig_mc = current_time() - start_time;

//  dummy1.check_invariant();
  std::cout << "Check Original design using transformed design\n";
  start_time = current_time();
  
  interpolationt_netlist dummy(cmdline);
  
  interpolation_coveraget ictorig(cmdline, working_netlist, force_selects_node,
                                  force_selects_latch, dummy, false);

  ictorig.set_netlist(working_netlist);
  ictorig.set_bound(this->bound);
  ictorig.set_bound(1);
  ictorig.set_unrolling_type(KEN); //Ken
  ictorig.set_coverage(false); //Ken
  ictorig.set_induction(false);  
  ictorig.set_minimize(true);
  int result1 = ictorig.do_interpolation();
    //returns 0 for CE
    //return 1 for fixed point
  if(result1 == 0)
  {
    std::cout << "Assertion failed\n";
    return 1;
  }
  
  assert(result1 == 1);
  fine_timet time_orig_new_mc = current_time() - start_time;

  ictorig.check_invariant();
  start_time = current_time();
  
  const interpolation_resolution_prooft &original_proof = ictorig.get_final_resolution_proof();
  unsigned number_of_interpolants = ictorig.get_size_of_interpolants();
  
    //the selectos absent in the core are not 
    //covered as they do not contribute
  std::cout << "Start Coverage Tests\n";
  log << "Test 1: checking original core for absence of selectors\n";
  check_coret c = check_coret(original_proof, ictorig.return_bound(), 
                              working_netlist, force_selects_node, force_selects_latch);
  c.check_original_core();
  log << "Results of core test after interpolation\n";
  core_test.print();
  
    //get the clauses involved in the last proof and 
    ///check these.
    //remove the rest of the multiplexors one by one and 
    //check if the invariant found before is still valid
  induction_coveraget indct(cmdline, working_netlist, force_selects_node,
                            force_selects_latch, 
                            ictorig);
  
  indct.do_coverage();
  
/* 
  std::cout << "Test 3: Moving on to interpolation-based tests\n";
  interpolation_coveraget ict(cmdline, working_netlist, force_selects_node,
                              force_selects_latch,
                              ictorig);
  ict.do_coverage();
*/
  print_result_per_latch();
  print_total_stats();

  core_test.print();
  ce_test.print();
  induction_test.print();
  induction_test_from_scratch.print();
  interpolation_test.print();
  log << "Time needed for coverage analysis = " << time2string(current_time() - start_time) << std::endl;  
  log << "Time needed for Original model checking = " << time2string(time_orig_mc) << std::endl;
  log << "Time needed Original model checking using transformed model = " << time2string(time_orig_new_mc) << std::endl;
  
  return 1;
}



void coveraget::print_result_per_latch()
{
  for(std::map< std::string, force_multiplexert>::iterator iter = force_selects_latch.begin();
      iter != force_selects_latch.end(); iter++)
  {
    std::string result = (*iter).second.coverage.at(2).result == COVERED ? "really covered" : "NOTcovered";
    std::string method = (*iter).second.coverage.at(2).get_method();
    
    log << (*iter).first << " is NONDET " << result << " by " << method << std::endl;
    result = (*iter).second.coverage.at(1).result == COVERED ? "really covered" : "NOTcovered";

    method = (*iter).second.coverage.at(1).get_method();

    log << (*iter).first << " is ONE " << result << " by " << method << std::endl;
    result = (*iter).second.coverage.at(0).result == COVERED ? "really covered" : "NOTcovered";

    method = (*iter).second.coverage.at(0).get_method();
    log << (*iter).first << " is ZERO " << result << " by " << method << std::endl;
  }
}


void coveraget::print_total_stats()
{
  unsigned total = force_selects_latch.size();
  total = total + force_selects_node.size();
  unsigned notcovered_nondet = 0;
  unsigned notcovered_zero = 0;
  unsigned notcovered_one = 0;
  
  unsigned method_core = 0;
  unsigned method_induction = 0;
  unsigned method_induction_from_scratch = 0;
  unsigned method_induction_from_scratch_skip = 0;
  unsigned method_interpolation = 0;
  unsigned method_interpolation_skip = 0;
  
  for(std::map< std::string, force_multiplexert>::iterator iter = force_selects_latch.begin();
      iter != force_selects_latch.end(); iter++)
  {
    if((*iter).second.coverage.at(2).result == NOTCOVERED)
    {
      log << (*iter).first << " is NONDET notcovered\n";
      notcovered_nondet++;
    }    
    else 
    { 
      if((*iter).second.coverage.at(1).result == NOTCOVERED)
      {
        log << (*iter).first << " is ONE notcovered\n";      
        notcovered_one++;
      }    
      if((*iter).second.coverage.at(0).result == NOTCOVERED)
      {
        log << (*iter).first << " is ZERO notcovered\n";
        notcovered_zero++;
      }
    }  
  }
  
  
    
/*      (*iter).second.coverage.at(2).method == CORE ? method_core++ : 
      (*iter).second.coverage.at(2).method == INDUCTION ? method_induction++ : 
      (*iter).second.coverage.at(2).method == INDUCTION_SCRATCH ? method_induction_from_scratch++ : 
      (*iter).second.coverage.at(2).method == INDUCTION_SCRATCH_SKIP ? method_induction_from_scratch_skip++: 
      (*iter).second.coverage.at(2).method == INTERPOLATION ? method_interpolation++ : 
      (*iter).second.coverage.at(2).method == INTERPOLATION_SKIP ? method_interpolation_skip++ : method_interpolation_skip+1-1;

    (*iter).second.coverage.at(1).method == CORE ? method_core++ : 
      (*iter).second.coverage.at(1).method == INDUCTION ? method_induction++ : 
      (*iter).second.coverage.at(1).method == INDUCTION_SCRATCH ? method_induction_from_scratch++ : 
        (*iter).second.coverage.at(1).method == INDUCTION_SCRATCH_SKIP ? method_induction_from_scratch_skip++: 
        (*iter).second.coverage.at(1).method == INTERPOLATION ? method_interpolation++ : 
        (*iter).second.coverage.at(2).method == INTERPOLATION_SKIP ? method_interpolation_skip++ : method_interpolation_skip+1-1;

    (*iter).second.coverage.at(0).method == CORE ? method_core++ : 
      (*iter).second.coverage.at(0).method == INDUCTION ? method_induction++ : 
      (*iter).second.coverage.at(0).method == INDUCTION_SCRATCH ? method_induction_from_scratch++ : 
      (*iter).second.coverage.at(0).method == INDUCTION_SCRATCH_SKIP ? method_induction_from_scratch_skip++: 
      (*iter).second.coverage.at(0).method == INTERPOLATION ? method_interpolation++ : 
      (*iter).second.coverage.at(2).method == INTERPOLATION_SKIP ? method_interpolation_skip++ : method_interpolation_skip+1-1;
*/
  

  log << "Total number of latches = " << total << std::endl;   
  log << (100*notcovered_nondet)/total << "% latches NONDET notcovered.\n";
  log << 100*notcovered_one/total << "% latches ONE notcovered.\n";
  log << 100*notcovered_zero/total << "% latches ZERO notcovered.\n";
  
/*  std::cout << "Number of NOTcoverd latches using CORE test=" << method_core << " %=" << 100*method_core/(total*3) << std::endl;
  std::cout << "Number of Induction test conclusive=" << method_induction << " %=" << 100*method_induction/(total*3) << std::endl;

  std::cout << "Number of Induction from scratch test conclusive=" << method_induction_from_scratch << " %=" << 
    100*method_induction_from_scratch/(total*3) << std::endl;
  std::cout << "Number of Induction from scratch skipped test conclusive="<< method_induction_from_scratch_skip << " %=" << 
    100*method_induction_from_scratch_skip/(total*3) << std::endl;

  std::cout << "Number of Interpolation test conclusive=" << method_interpolation << " %=" << 100*method_interpolation/(total*3) << std::endl;
  std::cout << "Number of Interpolation skip test conclusive=" << method_interpolation_skip << " %=" << 100*method_interpolation_skip/(total*3) << std::endl;
*/
}

