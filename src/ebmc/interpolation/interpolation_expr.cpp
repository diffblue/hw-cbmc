/*******************************************************************\

Module: Interpolation

Author: Mitra Purandare

\*******************************************************************/
#include "interpolation_expr.h"
#if 0
/*******************************************************************\

Function: do_interpolation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int do_interpolation(
  const cmdlinet &cmdline)
{
  interpolationt interpolation(cmdline);
  
  return interpolation.do_interpolation();
}

/*******************************************************************\

Function: interpolationt::do_interpolation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int interpolationt::do_interpolation()
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

    // check the initial state
  result=check_initial_state();
  if(result==-1){
      
      // now do main loop
    iteration_number=0;
    //bound=1; // start with 2 time frames
    get_bound();
    do
    {
      result=iteration();
      getchar();
    }
    while(result==-1);
  }
  std::cout << "Total time = " << time2string(current_time()-start_time) << std::endl;
  std::cout << "SAT time = " << time2string(sat_time) << std::endl;
  return result;
}

/*******************************************************************\

Function: interpolationt::check_initial_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int interpolationt::check_initial_state()
{
  status("Checking initial state");

  satcheckt satcheck;
  boolbvt solver(satcheck);
  namespacet ns(context);

    // check if I AND !P is satisfiable
  
  unwind(solver, 1, true);

  status("construct property");

  property(
    prop_expr_list,
    prop_bv,
    *this, // message
    solver,
    1, // timeframes
    ns);
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

      trans_tracet trans_trace;
  
      compute_trans_trace(
        prop_expr_list,
        prop_bv,
        solver,
        1, // 1 timeframe
        ns,
        main_symbol->name,
        trans_trace);
        
      if(get_ui()==ui_message_handlert::PLAIN)
        result("Counterexample:\n");

      show_trans_trace(
        trans_trace,
        *this, // message
        ns,
        get_ui());
        
      if(cmdline.isset("dump-vcd"))
      {
        std::string vcdfile =std::string(cmdline.getval("dump-vcd"));
        std::ofstream vcd(vcdfile.c_str());
        show_trans_trace_vcd(
          trans_trace,
          *this, // message
          ns,
          get_ui(), vcd);
        vcd.close();
      }      

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

Function: interpolationt::build_variable_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void my_find_symbols(
  const exprt &src,
  std::set<exprt> &dest,
  bool current,
  bool next)
{
  if((src.id()=="symbol" && current) ||
     (src.id()=="next_symbol" && next) ||
     (src.id()=="nondet_symbol"))
    dest.insert(src);
  else
  {
    forall_operands(it, src)
      my_find_symbols(*it, dest, current, next);
  }
}

void interpolationt::build_variable_map(
  boolbvt &boolbv)
{
  variable_map.clear();
  variable_names.clear();
    // collect all the symbols in the model and the property
  typedef hash_set_cont<irep_idt, irep_id_hash> symbolst;
  std::set<exprt> symbols;
  
  my_find_symbols(*trans_expr, symbols, true, true);

  for(prop_expr_listt::const_iterator
        it=prop_expr_list.begin();
      it!=prop_expr_list.end();
      it++)
    my_find_symbols(*it, symbols, true, true);

    // convert
  for(std::set<exprt>::const_iterator it=symbols.begin();
      it!=symbols.end();
      it++)
  {
    namespacet ns(context);
    //const symbolt &symbol=ns.lookup(*it);
    
    //exprt e0(symbol_expr(symbol));
    //exprt e1(symbol_expr(symbol));
    exprt e0(*it);
    exprt e1(*it);
    
    instantiate(e0, 0, ns);
    instantiate(e1, 1, ns);
    
    bvt bv0, bv1;
    
    boolbv.convert_bv(e0, bv0);
    boolbv.convert_bv(e1, bv1);
    
    assert(bv0.size()==bv1.size());
    
    for(unsigned i=0; i<bv0.size(); i++)
    {
      assert(!bv0[i].sign());
      assert(!bv1[i].sign());
      variable_map[bv1[i].var_no()]=bv0[i].var_no();

      variable_names[bv0[i].var_no()]=
        timeframe_identifier(0, it->get("identifier"))+"["+i2string(i)+"]";
      status(i2string(bv0[i].var_no()) + "= " + variable_names[bv0[i].var_no()]);

      variable_names[bv1[i].var_no()]=
        timeframe_identifier(1, it->get("identifier"))+"["+i2string(i)+"]";
      status(i2string(bv1[i].var_no()) + "= " + variable_names[bv1[i].var_no()]);
    }
  }
}

/*******************************************************************\

Function: interpolationt::iteration

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int interpolationt::iteration()
{
  iteration_number++;
  std::cout << "Iteration " << iteration_number << std::endl;
  std::cout << "Bound= " << bound << std::endl;
  status("Iteration "+i2string(iteration_number)+
         ", bound="+i2string(bound));

  if(iteration_number==100)
  {
    error("Exceeded iteration limit");
    return 1;
  }

  namespacet ns(context);
  interpolatort interpolator;
  boolbvt solver(interpolator);
  solver.equality_propagation=false;
  
    // build variable map
  build_variable_map(solver);

    // build formula
  interpolator.set_partition_id(1);
  build_partition1(solver);

  solver.clear_cache();  
  interpolator.set_partition_id(2);
  build_partition2(solver);
  build_property(solver);

    // solver
  fine_timet sat_start_time=current_time();
  decision_proceduret::resultt dec_result=
    solver.dec_solve();
  sat_time += current_time()-sat_start_time;
  switch(dec_result)
  {
    case decision_proceduret::D_SATISFIABLE:
      if(interpolants.empty())
      {
        result("SAT: bug found. Bound=" + i2string(bound));
        result("Iteration " + i2string(iteration_number));
        result("Bound=" + i2string(bound));

        trans_tracet trans_trace;
  
        compute_trans_trace(
          prop_expr_list,
          prop_bv,
          solver,
          bound+1,
          ns,
          main_symbol->name,
          trans_trace);
        
        if(get_ui()==ui_message_handlert::PLAIN)
          result("Counterexample:\n");

        show_trans_trace(
          trans_trace,
          *this, // message
          ns,
          get_ui());
        
        if(cmdline.isset("dump-vcd"))
        {
          std::string vcdfile =std::string(cmdline.getval("dump-vcd"));
          std::ofstream vcd(vcdfile.c_str());
          show_trans_trace_vcd(
            trans_trace,
            *this, // message
            ns,
            get_ui(), vcd);
          vcd.close();
        }      

        report_failure();
        return 0;
      }
      else
      {
        status("SAT: interpolation failed, increasing bound");
        bound = bound + interpolants.size();
        interpolants.clear();
          //      bound++;
      }
      break;

    case decision_proceduret::D_UNSATISFIABLE:
      status("UNSAT: getting interpolant, doing widening");

      {

        get_interpolant(interpolator);
        if(reached_fixedpoint())
          return 0;
      }
        //    bool do_induction = false;
        //see if induction succeeds
      if(!cmdline.isset("stop-induction"))
      {
        int result=induction_step();
        return result;
      }
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

Function: interpolationt::reached_fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool interpolationt::reached_fixedpoint()
{
  status("Checking whether we reached a fixed-point");
  if(interpolants.size() == 1)
    return false;

  const bit_interpolantt &new_interpolant = interpolants.back();

  if(new_interpolant.is_false()) return true;

  satcheckt solver;
  namespacet ns(context);
    // "old" set of states
  status("interpolants.size() " + i2string(interpolants.size()));

  literalt l_old = const_literal(false);

/*  for(unsigned size = 0;
      size < interpolants.size(); size++)
    interpolants.at(size).add_variables(solver);
*/  
  for(unsigned size = 0;
      size < interpolants.size()-1; size++)
  {
//    literalt l_old_1 = interpolants.at(size).convert(solver);
    literalt l_old_1 = interpolants.at(size).instantiate(netlist_bmc_map, solver);
    l_old=solver.lor(l_old, l_old_1);
  }

  status("converted old interpolants");

  {
    boolbvt prop_conv(solver);
    literalt l_init=
      instantiate_convert(prop_conv, trans_expr->init(),  0, ns);
    l_old=solver.lor(l_old, l_init);
  }

    // "new" set of states
  literalt l_new = new_interpolant.convert(solver);
    //  l_new=solver.lor(l_new, l_old); // we need to add this when we do not add all the 
    //previous interpolants to the initial states
    // check if l_new -> l_old = not l_new or l_old == not ( l_new and not l_old)
  solver.l_set_to(l_old, false);
  solver.l_set_to(l_new, true);

  switch(solver.prop_solve())
  {
    case propt::P_SATISFIABLE:
      status("SAT: fixed-point not yet reached");
      return false;

    case propt::P_UNSATISFIABLE:
      result("UNSAT: fixed-point reached.");
      result("property holds!");
      result("Iteration " + i2string(iteration_number));
      result("Bound=" + i2string(bound));
      return true;

    default:
      throw "unexpected result from SAT-solver";
  }
}
/*******************************************************************\

Function: interpolationt::get_interpolant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void interpolationt::get_interpolant(
  interpolatort &interpolator)
{

    //ok, get the interpolant
  status("current interpolants.size() :: " + i2string(interpolants.size()));

  do_interpolationt do_interpolation(interpolator.get_resolution_proof(), 1);
  bit_interpolantt inter = do_interpolation.get_interpolant();
  interpolants.push_back(inter); 
    //  interpolator.get_interpolant(1, 2, interpolants.back());
    //  interpolator.print_usages();
  std::cout << "size of interpolant " << interpolants.back().aig.number_of_nodes() << std::endl;
  //  std::cout << interpolants.back().aig << std::endl;
  check_partition_one_implies_interpolant();
  check_partition_two_and_interpolant();
  std::cout << "interpolant is " << std::endl;
  std::cout << interpolants.back() << std::endl;
#ifdef DEBUG
 const char *file_name = "bit_interpolant";
 std::ofstream sv(file_name, std::ios::app); 
 sv << interpolants.back().aig << std::endl;
#endif
  map_variables(interpolants.back());
    // TODO: make it smaller
//  std::cout << interpolants.back().aig << std::endl;
  
  if(!cmdline.isset("stop-minimize"))
  {
//    minimizert minimizer(interpolants.back(), interpolator.no_variables()-1, 32);
#ifdef DEBUG
    const char *fn = "aig_minimizer_log";
    std::ofstream ofn(fn, std::ios::out);
    minimizert minimizer(interpolants.back(), do_interpolation.no_primary_vars_in_interpolant(), 32, ofn);
#else
    minimizert minimizer(interpolants.back(), do_interpolation.no_primary_vars_in_interpolant(), 32);
#endif

    minimizer.minimize();
    
#ifdef DEBUG
    ofn.close();
#endif
  }
}

/*******************************************************************\

Function: interpolationt::map_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpolationt::map_variables(
  bit_interpolantt &f)
{
  for(aigt::nodest::iterator
        it=f.aig.nodes.begin();
      it!=f.aig.nodes.end();
      it++)
    if(it->is_var())
      map_literal(*it);
}

/*******************************************************************\

Function: interpolationt::map_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpolationt::map_literal(
  aig_nodet &l)
{
  variable_mapt::const_iterator it=variable_map.find(l.var_no());
  
  if(it==variable_map.end())
  {
      //sanity check..this shud be new intermediate literal added 
      //by the interpolation procedure
  }
  else
  {
    l.make_var(it->second);
  }
}

/*******************************************************************\

Function: interpolationt::build_partition1

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpolationt::build_partition1(
  prop_convt &solver)
{
  status("build_partition1");
  namespacet ns(context);

  if(interpolants.empty())
  {
    status("init when no interpolant");
    instantiate(solver, trans_expr->init(), 0, ns);
  }
  else
  {
    status("init with interpolant");

    bvt or_bv;
    //    interpolants.back().add_variables(solver.prop);
    literalt l_old_1 = interpolants.back().convert(solver.prop);
    or_bv.push_back(l_old_1);
    solver.prop.lcnf(or_bv);
  }

    // unwinding for one step
  status("instantiating invar");
  instantiate(solver, trans_expr->invar(), 0, ns);
  status("instantiating trans");
  instantiate(solver, trans_expr->trans(), 0, ns);
  status("build_partition1 done");
}

/*******************************************************************\

Function: interpolationt::build_partition2

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpolationt::build_partition2(
  prop_convt &solver)
{
  status("build_partition2");
  namespacet ns(context);
  unsigned no_timeframes=bound+1;

  const exprt &op_invar=trans_expr->invar();
  const exprt &op_trans=trans_expr->trans();

    // unwinding for frames 1,..,bound+1
  for(unsigned c=1; c<no_timeframes; c++)
    instantiate(solver, op_invar, c, ns);

    // unwinding for frames 1,..,bound+1
  for(unsigned c=1; c<no_timeframes-1; c++)
    instantiate(solver, op_trans, c, ns);

  status("build_partition2 done");
}

/*******************************************************************\

Function: interpolationt::build_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpolationt::build_property(
  prop_convt &solver)
{

  status("build_property");

  namespacet ns(context);
  unsigned no_timeframes=bound+1;
  unsigned start;

  if(!cmdline.isset("start"))
  {
    warning("using default start(1) for property building");
      //start=no_timeframes-1;
    start=1;
  }
  else
  {
    start=atoi(cmdline.getval("start"));
    if(start == 0)
      start = no_timeframes-1;
  }

    //  std::cout << "value of start " << start << std::endl;
  if(start > no_timeframes-1)
  {
    error("start > bound, reduce the value of start\n");
  }

  prop_bv.clear();
  
  bvt all_prop_bv;

  for(std::list<propertyt>::const_iterator
        it=properties.begin();
      it!=properties.end();
      it++)
  {
    prop_bv.push_back(bvt());

    exprt property(it->expr);

    if(property.id()!="AG" ||
       property.operands().size()!=1)
    {
      throw "unsupported property - only AGp implemented";
    }

    const exprt &p=property.op0();

      // time frames 0,...,k-1: just true
    for(unsigned c=0; c<no_timeframes-1; c++)
    {
      if(c>=start)
      {
        exprt tmp(p);
        instantiate(tmp, c, ns);
        literalt l=solver.convert(tmp);
        prop_bv.back().push_back(l);
        all_prop_bv.push_back(l);
      }
      else
        prop_bv.back().push_back(const_literal(true));
    }

      // claim: time frame k
    {
      exprt tmp(p);
      instantiate(tmp, no_timeframes-1, ns);
      literalt l=solver.convert(tmp);
      prop_bv.back().push_back(l);
      all_prop_bv.push_back(l);
    }
  }
  solver.prop.l_set_to(solver.prop.land(all_prop_bv), false);
  status("build_property done");
}

/*******************************************************************\

Function: interpolationt::check_partition_one_implies_interpolant

  Inputs:

 Outputs:

 Purpose: checks if (partition_1 -> computed_interpolant) is TRUE
Here, partition_1 is (initial_state OR previous_interpolants) AND trans AND invar

\*******************************************************************/
bool interpolationt::check_partition_one_implies_interpolant()
{
  status("Checking whether the interpolant is OK i.e. a->p");
  const bit_interpolantt &new_interpolant = interpolants.back();

  if(new_interpolant.is_false()) return false;

  namespacet ns(context);
  satcheckt solver;
  boolbvt boolbv(solver);
  boolbv.equality_propagation=false;
  build_variable_map(boolbv);

    // "old" set of states
    //  build_partition1(boolbv);
  status("build_partition1");

  if(interpolants.size()  == 1) // if its one then its the current interpolant which we do not want in the sanity check
  {
    status("init when no interpolant");
    instantiate(boolbv, trans_expr->init(), 0, ns);
  }
  else
  {
    status("init with interpolant");
    bvt or_bv;
    //    interpolants.at(interpolants.size()-2).add_variables(boolbv.prop);
    literalt l_old_1 = interpolants.at(interpolants.size()-2).convert(boolbv.prop);
    or_bv.push_back(l_old_1);
    boolbv.prop.lcnf(or_bv);
  }

  status("instantiating invar");
  instantiate(boolbv, trans_expr->invar(), 0, ns);
  status("instantiating trans");
  instantiate(boolbv, trans_expr->trans(), 0, ns);

  status("built_partition1");
  status("converting interpolant");
  //  new_interpolant.add_variables(solver);
  literalt l_new = new_interpolant.convert(solver);

  solver.l_set_to(l_new, false);

  switch(solver.prop_solve())
  {
    case propt::P_SATISFIABLE:
      status("sanity one false :: partition1->interpolant=false");
      exit(0);
      throw "interpolant incorrect :: partition1->interpolant is UNSAT";
      
    case propt::P_UNSATISFIABLE:
      result("sanity one true :: partition1->interpolant=true");
      return true;
    default:
      throw "unexpected result from SAT-solver";
  }
}

/*******************************************************************\

Function: interpolationt::check_partition_two_and_interpolant

  Inputs:

 Outputs:

 Purpose: checks if (computed_interpolant AND partition_2) is FALSE

\*******************************************************************/
bool interpolationt::check_partition_two_and_interpolant()
{
  status("Checking whether the interpolant is OK i.e. b and p = unsat");
  const bit_interpolantt &new_interpolant = interpolants.back();

  if(new_interpolant.is_false()) return false;

  namespacet ns(context);
  satcheckt solver;
  boolbvt boolbv(solver);
  boolbv.equality_propagation=false;
  build_variable_map(boolbv);

    // "old" set of states
  build_partition2(boolbv);
  build_property(boolbv);

  status("converting interpolant");
  //  std::cout << new_interpolant.aig << std::endl;
  //  new_interpolant.add_variables(solver);
  literalt l_new = new_interpolant.convert(solver);
  solver.l_set_to(l_new, true);

  switch(solver.prop_solve())
  {
    case propt::P_SATISFIABLE:
      status("sanity two true :: p and b = true");
      throw "interpolant incorrect :: b and p is SAT";
      exit(0);
    case propt::P_UNSATISFIABLE:
      result("sanity two false :: p and b = false");
      return true;

    default:
      throw "unexpected result from SAT-solver";
  }
}

int interpolationt::induction_step()
{
  status("Induction Step");

  namespacet ns(context);
  satcheckt satcheck;
  boolbvt solver(satcheck);
  
    // *no* initial state
  status("instantiating invar");
  instantiate(solver, trans_expr->invar(), 0, ns);
  status("instantiating trans");
  instantiate(solver, trans_expr->trans(), 0, ns);
  build_partition2(solver);
    //  build_property(solver);

  unsigned no_timeframes=bound+1;

    // *no* initial state
    //  unwind(solver, no_timeframes, false);


  for(std::list<propertyt>::const_iterator
        it=properties.begin();
      it!=properties.end();
      it++)
  {
    if(it->expr.is_true())
      continue;
  
    exprt property(it->expr);

    if(property.id()!="AG" ||
       property.operands().size()!=1)
    {
      error("unsupported property - only AGp implemented");
      return 1;
    }

    const exprt &p=property.op0();

      // assumption: time frames 0,...,k-1
    for(unsigned c=0; c<no_timeframes-1; c++)
    {
      exprt tmp(p);
      instantiate(tmp, c, ns);
      solver.set_to_true(tmp);
    }
    
      // claim: time frame k
    {
      exprt tmp(p);
      instantiate(tmp, no_timeframes-1, ns);
      solver.set_to_false(tmp);
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
      return 0;
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
#endif
