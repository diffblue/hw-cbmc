/*******************************************************************\

Module: Interpolation

Author: Mitra Purandare

\*******************************************************************/
#include <string>
#include <config.h>
#include <simplify_expr.h>

#include "interpolation_word.h"

#include <interpolation/wordlevel/rewrite_if.h>
#include <interpolation/bitlevel/bit_interpolant_print.h>


//std::map<mixed_interpolantt *, literalt> literal_cache;
//hash_map_cont<const exprt, literalt , irep_hash> literal_cache;
 
static std::string drop_timeframe_identifier(
  const irep_idt &identifier)
{
  std::string tf;
  std::string s = id2string(identifier);
  std::string::size_type t = s.find("@");
  if(t == std::string::npos)
   return s;

  tf = s.substr(t, 2);
  //HACK
  assert(tf == "@1" || tf == "@0");
  assert(t != std::string::npos);
  s.erase(t, 2);
  return s;
}

static void drop_timeframe_rec(
  exprt & expr)
{
  assert(expr.id() != "next_symbol");
  if(expr.id()=="symbol")
  {
    const irep_idt &identifier=expr.get("identifier");
    expr.set("identifier", drop_timeframe_identifier(identifier));
  }
  else
  {
    Forall_operands(it, expr)
      {
	drop_timeframe_rec(*it);
      }
  }
}
 

static void drop_timeframe(
  exprt &e)
{
  drop_timeframe_rec(e);
}


static void get_cache_map(
  const hash_map_cont<exprt, literalt, irep_hash>& cache, 
  std::set<skeleton_mapt> &skeleton_vars, 
  unsigned part_id,
 const namespacet &ns)
{
  hash_map_cont<exprt, literalt, irep_hash>::const_iterator cache_result = cache.begin();
  for(; cache_result != cache.end(); cache_result++)
  {
    exprt entry = (*cache_result).first;
    simplify(entry, ns);
    if(((entry.id() == "not") && entry.op0().id() == "symbol") || entry.id() == "symbol" || entry.id() == "next_symbol")
      {
	//	std::cout << "expr is " << (*cache_result).first.pretty() << std::endl;
	//	getchar();
      }
    else if(entry.id() == "extractbit")
      {
	//	std::cout << "extract bit is " << (*cache_result).first.pretty() << std::endl;	
	//	getchar();
      }
    else
      {
	//	std::cout << "expr is " << (*cache_result).first.pretty() << std::endl;
	//	getchar();
	//    std::cout << "literal is " << (*cache_result).second.dimacs() << std::endl;
	skeleton_mapt skel((*cache_result).second, entry, part_id);
	skeleton_vars.insert(skel);
      }
  }
}

/*******************************************************************\

Function: do_interpolation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int do_interpolation_word(
  const cmdlinet &cmdline)
{
  interpolationt_word interpolation(cmdline);
  
  return interpolation.do_interpolation();
}

/*******************************************************************\

Function: interpolationt::do_interpolation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int interpolationt_word::do_interpolation()
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
    get_bound();
    std::cout << "bound is " << bound << std::endl;
      //  bound=1; // start with 2 time frames

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

Function: interpolationt_word::check_initial_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int interpolationt_word::check_initial_state()
{
  status("Checking initial state");

  namespacet ns(symbol_table);
  satcheckt satcheck;
  boolbvt solver(ns, satcheck);

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

Function: interpolationt_word::build_variable_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
static void my_find_symbols(
  const exprt &src,
  std::set<exprt> &dest,
  bool current,
  bool next)
{
  if((src.id()=="symbol" && current) ||
     //     (src.id()=="next_symbol" && next) ||
     (src.id()=="nondet_symbol"))
    dest.insert(src);
  else
  {
    forall_operands(it, src)
      my_find_symbols(*it, dest, current, next);
  }
}
void interpolationt_word::build_variable_map(
  boolbvt &boolbv)
{
  std::set<exprt> symbols;
  
  my_find_symbols(*trans_expr, symbols, true, true);

  for(prop_expr_listt::const_iterator
        it=prop_expr_list.begin();
      it!=prop_expr_list.end();
      it++)
    my_find_symbols(*it, symbols, true, true);


    // collect all the symbols in the model and the property
  for(std::set<exprt>::const_iterator it=symbols.begin();
      it!=symbols.end();
      it++)
  {
    namespacet ns(symbol_table);

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
      
      if(reverse_map.size() < bv0[i].var_no()+1)
        reverse_map.resize(bv0[i].var_no()+1);

      assert(reverse_map.size() >= bv0[i].var_no()+1);
      
      assert(e0.id() == "symbol" || e0.id() == "next_symbol" || e0.id() == "nondet_symbol");
      
//      bv_varidt bvi0(e0.get("identifier"),i);
      bv_exprt bvi0(e0, i);
      
      reverse_map[bv0[i].var_no()] = bvi0;
      
      if(reverse_map.size() < bv1[i].var_no()+1)
        reverse_map.resize(bv1[i].var_no()+1);

      assert(reverse_map.size() >= bv1[i].var_no());

      assert((e0.id() == "symbol") || (e0.id() == "next_symbol") || e0.id() == "nondet_symbol") ;
//      bv_varidt bvi1(e1.get("identifier"), i);
      bv_exprt bvi1(e1, i);
      reverse_map[bv1[i].var_no()] = bvi1;
      
      
      variable_names[bv0[i].var_no()]=
        timeframe_identifier(0, it->get("identifier"))+"["+i2string(i)+"]";
      status(i2string(bv0[i].var_no()) + "= " + variable_names[bv0[i].var_no()]);
#ifdef DEBUG
//      std::cout << bv0[i].var_no() << "= " << variable_names[bv0[i].var_no()] << std::endl;
#endif
      variable_names[bv1[i].var_no()]=
        timeframe_identifier(1, it->get("identifier"))+"["+i2string(i)+"]";

      status(i2string(bv1[i].var_no()) + "= " + variable_names[bv1[i].var_no()]);
#ifdef DEBUG
//      std::cout << bv1[i].var_no() << "= " << variable_names[bv1[i].var_no()] << std::endl;
#endif
    }
  }
}

/*******************************************************************\

Function: interpolationt_word::iteration

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int interpolationt_word::iteration()
{
  iteration_number++;
  std::cout << "Iteration " << iteration_number << std::endl;
  std::cout << "Bound= " << bound << std::endl;
  status("Iteration "+i2string(iteration_number)+
         ", bound="+i2string(bound));

  //	if(iteration_number == 5)
  //	  return 0;
  if(iteration_number==100)
  {
    error("Exceeded iteration limit");
    return 1;
  }

  namespacet ns(symbol_table);
  interpolatort interpolator;
  boolbvt solver(ns, interpolator);
  solver.equality_propagation=false;
  
    // build variable map
  build_variable_map(solver);

    // build formula
  interpolator.set_partition_id(1);

  skeleton_vars.clear();
  build_partition1(solver);

  const hash_map_cont<exprt, literalt, irep_hash>& cache =  solver.get_cache();
  get_cache_map(cache, skeleton_vars, 1, ns);
  solver.clear_cache();  
  
  const hash_map_cont<exprt, literalt, irep_hash>& cache1 =  solver.get_cache();  
  assert(cache1.empty());

  //  std::cout << "size of proof " << interpolator.get_resolution_proof().r_steps.size() << std::endl;

  interpolator.set_partition_id(2);

  build_partition2(solver);
  //  std::cout << "size of proof " << interpolator.get_resolution_proof().r_steps.size() << std::endl;
  build_property(solver);
  //  std::cout << "size of proof " << interpolator.get_resolution_proof().r_steps.size() << std::endl;
  get_cache_map(cache, skeleton_vars, 2, ns);
  solver.clear_cache();
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
//        bound = bound + interpolants.size();
        bound++;
        interpolants.clear();
      }
      break;

    case decision_proceduret::D_UNSATISFIABLE:
      status("UNSAT: getting interpolant, doing widening");
      {
        get_interpolant(solver, interpolator);


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

Function: interpolationt_word::reached_fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool interpolationt_word::reached_fixedpoint()
{
  status("Checking whether we reached a fixed-point");
  status("interpolants.size() " + i2string(interpolants.size()));

  if(interpolants.size() == 1)
    return false;

    //make an expression for the fixed point
    //and throw it to the SAT solver

  const exprt &new_interpolant = interpolants.back();
  if(new_interpolant.is_false()) return true;

  satcheckt solver;
  namespacet ns(symbol_table);
  boolbvt prop_conv(ns, solver);
  build_variable_map(prop_conv);
    // "old" set of states

  literalt l_old = const_literal(false);
  for(unsigned size = 0;
      size < interpolants.size()-1; size++)
  {
    literalt l_int = start_instantiate_convert(prop_conv, interpolants.at(size), ns);
    l_old=solver.lor(l_old, l_int);

  }
  status("converted old interpolants");

  {
    literalt l_init = instantiate_convert(prop_conv, trans_expr->init(),  0, ns);
    l_old=solver.lor(l_old, l_init);

  }

    // "new" set of states
  literalt l_new = start_instantiate_convert(prop_conv, new_interpolant, ns);
 
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

void interpolationt_word::get_interpolant(
  boolbvt& solver, 
  interpolatort &interpolator)
{
  /*
  {
    std::vector<bool> skl(interpolator.get_resolution_proof().no_vars, false);
    const char *op_name = "rem_un_cl_proof";
    std::ofstream op(op_name, std::ios::out);

    interpolator.get_resolution_proof().print_proof_in_dot(
							   interpolator.get_resolution_proof().empty_clause_id, 
							   op, skl);

    op.close();
  }
*/

  //  interpolator.get_resolution_proof().remove_unused_clauses();
  std::string use_tool = cmdline.isset("interpolator") ? std::string(cmdline.getval("interpolator")) : std::string("ebvi");
  

  if(use_tool.compare("foci") == 0 || use_tool.compare("csi") == 0)
  {
      // use csi-sat
    cmdlinet cmd;
    config.set(cmd);
  }
#ifdef DEBUG
  interpolator.get_resolution_proof().check_proof(interpolator.get_resolution_proof().empty_clause_id);
#endif
  /*  bit_interpolantt inter_ken2;
  
  {  
    satcheck_bit_interpolation_normalt do_interpolation(interpolator.get_resolution_proof(), 1);
    inter_ken2 = do_interpolation.get_interpolant();
    //    std::cout << "Before " << inter_ken << std::endl;
  
    mixed_interpolantt *interpolant_ken = new mixed_interpolantt();
    interpolant_ken->ntype = mixed_interpolantt::ROOT;
    interpolant_ken->expr = false;
    interpolant_ken->interpolant_aig = inter_ken2;
    bool p1b = check_partition_one_implies_interpolant(interpolant_ken);
    bool p2b= check_partition_two_and_interpolant(interpolant_ken);
    if(!p1b || !p2b)
      {
	std::cout << "BIT Before Before Before interpolant incorrect\n";
	assert(0);
      }
  }
  */

  do_interpolationt do_word_interpolation(interpolator.get_resolution_proof(), skeleton_vars, reverse_map);
  if(use_tool.compare("csi") == 0)
    do_word_interpolation.interpolator = 1; //csi
  else if(use_tool.compare("foci") == 0)
    do_word_interpolation.interpolator = 2; //foci
  else
    do_word_interpolation.interpolator = 0; //ebvi
  
  do_word_interpolation.proof_transform();
  //exit(0);
  exprt interpolant;
  if(do_word_interpolation.interpolator > 0)
  {
    expr_listt interpolant_list = do_word_interpolation.get_interpolant_list();
    assert(interpolant_list.size() == 1);
    interpolant = (*(interpolant_list.begin()));
  }
  else
    {
      expr_listt interpolant_list = do_word_interpolation.get_interpolant_list();
      interpolant = (*(interpolant_list.begin()));
      //      interpolant = do_word_interpolation.get_interpolant(1);
    }

  namespacet ns(symbol_table);
  simplify(interpolant, ns);
  /*  {
    
    satcheck_bit_interpolation_normalt do_interpolation(interpolator.get_resolution_proof(), 1);
    bit_interpolantt inter_ken = do_interpolation.get_interpolant();
    mixed_interpolantt *interpolant_ken = new mixed_interpolantt();
    interpolant_ken->ntype = mixed_interpolantt::ROOT;
    interpolant_ken->expr = false;
    interpolant_ken->interpolant_aig = inter_ken;
    bool p1b = check_partition_one_implies_interpolant(interpolant_ken);
    bool p2b= check_partition_two_and_interpolant(interpolant_ken);
    if(!p1b || !p2b)
    {
      std::cout << "BIT interpolant after incorrect\n";
    }
  }
  */

  simplify(interpolant, ns);
  /*
  std::cout << "######PRINTING\n";
  std::cout << expr2verilog(interpolant) << std::endl;
  std::cout << "######PRINTED\n";
*/
  

#ifdef DEBUG
  bool p1 = check_partition_one_implies_interpolant(interpolant);
  bool p2= check_partition_two_and_interpolant(interpolant);
  if(!p1 || !p2)
    assert(0);
#endif
// interpolant is in timeframe1..drop the timeframes.
  map_to_timeframe_zero(interpolant);

  interpolants.push_back(interpolant); 
}

/*******************************************************************\

Function: interpolationt_word::build_partition1

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpolationt_word::build_partition1(
  prop_convt &solver)
{
  status("build_partition1");
  namespacet ns(symbol_table);

  if(interpolants.empty())
  {
    status("11 init when no interpolant");
    instantiate_with_if_lifting(solver, trans_expr->init(), 0);
  }
  else
  {
    status("init with interpolant");
    bvt or_bv;
    std::cout << "START inserting the interpolant\n";
    literalt l_old_1 = start_instantiate_convert(solver, interpolants.back(), ns);

    std::cout << "DONE inserting the interpolant\n";
    solver.prop.l_set_to(l_old_1, true);
  }

    // unwinding for one step
  status("instantiating invar");
  instantiate_with_if_lifting(solver, trans_expr->invar(), 0);
  
  std::cout << "DONE INVAR\n";
  
  status("instantiating trans");
  instantiate_with_if_lifting(solver, trans_expr->trans(), 0);
  status("build_partition1 done");
}

/*******************************************************************\

Function: interpolationt_word::build_partition2

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpolationt_word::build_partition2(
  prop_convt &solver)
{
  status("build_partition2");
  namespacet ns(symbol_table);
  unsigned no_timeframes=bound+1;

  const exprt &op_invar=trans_expr->invar();
  const exprt &op_trans=trans_expr->trans();

    // unwinding for frames 1,..,bound+1
  for(unsigned c=1; c<no_timeframes; c++)
    instantiate_with_if_lifting(solver, op_invar, c);

  std::cout << "DONE INVAR\n";

    // unwinding for frames 1,..,bound+1
  for(unsigned c=1; c<no_timeframes-1; c++)
    instantiate_with_if_lifting(solver, op_trans, c);

  status("build_partition2 done");
}

/*******************************************************************\

Function: interpolationt_word::build_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interpolationt_word::build_property(
  prop_convt &solver)
{

  status("build_property");

  namespacet ns(symbol_table);
  unsigned no_timeframes=bound+1;
  unsigned start;

  if(!cmdline.isset("start"))
  {
      // warning("using default start(1) for property building");
      //start=no_timeframes-1;
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
  exprt tmp1;
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
      //start anding the expressions for skeleton map
      // time frames 0,...,k-1: just true
    bool start = true;
    for(unsigned c=0; c<no_timeframes-1; c++)
    {
      exprt tmp(p);
      if(c>=start)
      {
        instantiate(tmp, c, ns);
        literalt l=solver.convert(tmp);
        prop_bv.back().push_back(l);
        all_prop_bv.push_back(l);
        if(start)
          tmp1 = tmp;
        else
          tmp1 = gen_and(tmp1, tmp);
        start = false;
      }
      else
        prop_bv.back().push_back(const_literal(true));
    }

      // claim: time frame k
    {
      exprt tmp(p);
      instantiate(tmp, no_timeframes-1, ns);
      if(start)
        tmp1 = tmp;
      else
        tmp1 = gen_and(tmp1, tmp);
      literalt l=solver.convert(tmp);
      //      std::cout << "property " << l.dimacs() << std::endl;
      prop_bv.back().push_back(l);
      all_prop_bv.push_back(l);
    }
  }
  literalt l = solver.prop.land(all_prop_bv);
  //   std::cout << "property " << l.dimacs() << std::endl;
    //  exprt e;
  skeleton_mapt skm(l,tmp1,2);
  skeleton_vars.insert(skm);
  solver.prop.l_set_to(l, false);
  status("build_property done");
}

int interpolationt_word::induction_step()
{
  status("Induction Step");

  namespacet ns(symbol_table);
  satcheckt satcheck;
  boolbvt solver(ns, satcheck);
  
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

void interpolationt_word::map_to_timeframe_zero(exprt &t1)
{
  drop_timeframe(t1);
}

literalt interpolationt_word::start_instantiate_convert(
  prop_convt &prop_conv,
  const exprt &t1,
  const namespacet & ns)
{
  literalt l = instantiate_convert(prop_conv, t1, 0, ns);
  return l;

  /*  std::map<mixed_interpolantt *, literalt> ::iterator it = literal_cache.find(t1);
  if(it != literal_cache.end())
    return (*it).second;

  if(t1->ntype == mixed_interpolantt::ROOT)
  {
    if(t1->expr)
    {

      literalt l = instantiate_convert(prop_conv, t1->interpolant_expr, 0, ns);
      literal_cache.insert(std::make_pair(t1, l));
      return l;
    }
    else
    {
      //      t1->interpolant_aig.add_variables(prop_conv.prop);
      literalt l = t1->interpolant_aig.convert(prop_conv.prop);
      literal_cache.insert(std::make_pair(t1, l));
      return l;
    }
  }
  else
  {

    literalt l34;
    literalt l1 = start_instantiate_convert(prop_conv, t1->interpolant_left, ns);
    literalt l2 = start_instantiate_convert(prop_conv, t1->interpolant_right, ns);

    if(t1->ntype == mixed_interpolantt::AND)
      l34 = prop_conv.prop.land(l1, l2);
    else
      l34 = prop_conv.prop.lor(l1, l2);
    
    literal_cache.insert(std::make_pair(t1, l34));
    return l34;
  }
  */
}

void interpolationt_word::instantiate_with_if_lifting(prop_convt &solver,
                                                      const exprt &expr,
                                                      unsigned tf)
{
  exprt tmp(expr);
  
  namespacet ns(symbol_table);
  //  std::cout << "tmp is " << tmp.pretty() << std::endl;  
  rewrite_ift rewrite_if(tmp);
  rewrite_if();

  //  std::cout << "rewritten tmp is " << tmp.pretty() << std::endl;
  instantiate(solver, tmp, tf, ns);
}


literalt interpolationt_word::instantiate_convert_with_if_lifting(prop_convt &solver,
								  const exprt &expr,
								  unsigned tf)
{
  exprt tmp(expr);
  
  namespacet ns(symbol_table);
  
  rewrite_ift rewrite_if(tmp);
  rewrite_if();
  
  return instantiate_convert(solver, tmp, tf, ns);
}

bool interpolationt_word::check_partition_one_implies_interpolant(const exprt &t)
{
  //assert(0);
  status("Checking whether the interpolant is OK i.e. a->p");

  if(t.is_false()) return false;
  
  namespacet ns(symbol_table);
  satcheckt solver;
  boolbvt boolbv(ns, solver);
  //  boolbv.equality_propagation=false;
  build_variable_map(boolbv);

  literalt l_old;
  
  if(interpolants.empty())
  {
    status("11 init when no interpolant");
    l_old = instantiate_convert(boolbv, trans_expr->init(), 0, ns);
  }
  else
  {
    status("init with interpolant");
    l_old = start_instantiate_convert(boolbv, interpolants.back(), ns);
  }

    // unwinding for one step
  status("instantiating invar");
  literalt l_invar = instantiate_convert(boolbv, trans_expr->invar(), 0, ns);
  
  std::cout << "DONE INVAR\n";
  
  status("instantiating trans");
  literalt l_trans = instantiate_convert(boolbv, trans_expr->trans(), 0, ns);
  status("build_partition1 done");
  literalt part1 = solver.land(solver.land(l_invar, l_trans), l_old);

  status("build_partition1");

  literalt l_new = convert_as_it_is(boolbv, t);

    // check if partition1 -> interpolant = (not( partition1 and not interpolant))
  solver.l_set_to(l_new, false);
  solver.l_set_to(part1, true);
  
  switch(solver.prop_solve())
  {
    case propt::P_SATISFIABLE:
    {
      status("sanity one false :: partition1->interpolant=false");
      std::cout << "interpolant incorrect :: partition1->interpolant is UNSAT\n";
      return false;
//      assert(0);
      break;
    }
    case propt::P_UNSATISFIABLE:
    {
      result("sanity one true :: partition1->interpolant=true");
      return true;
    }
    default:
    {
      std::cout << "unexpected result from SAT-solver";
      assert(0);
    }
  }
  return false;
}

bool interpolationt_word::check_partition_two_and_interpolant(const exprt &t)
{
  status("Checking whether the interpolant is OK i.e. b and p = unsat");

  if(t.is_false()) return false;

  namespacet ns(symbol_table);
  satcheckt solver;
  boolbvt boolbv(ns, solver);
  boolbv.equality_propagation=false;
  build_variable_map(boolbv);

    // "old" set of states
  build_partition2(boolbv);
  build_property(boolbv);

  literalt l_new = convert_as_it_is(boolbv, t);

  solver.l_set_to(l_new, true);

  switch(solver.prop_solve())
  {
    case propt::P_SATISFIABLE:
      {
      status("sanity two true :: p and b = true");
      std::cout << "interpolant incorrect :: b and p is SAT\n";
      return false;
//      assert(0);
      }
    case propt::P_UNSATISFIABLE:
      {
      result("sanity two false :: p and b = false");
      return true;
      }
    default:
      {
	std::cout << "unexpected result from SAT-solver\n";
	assert(0);
      }
  }
}

literalt interpolationt_word::convert_as_it_is(
  prop_convt &prop_conv,
  const exprt &t1)
{
  literalt l = prop_conv.convert(t1);
  return l;
  /*
  hash_map_cont<const exprt, literalt, irep_hash >::iterator it = literal_cache.find(t1);
  if(it != literal_cache.end())
    return (*it).second;

  if(t1->ntype == mixed_interpolantt::ROOT)
  {
    if(t1->expr)
    {
      literalt l = prop_conv.convert(t1->interpolant_expr);
      literal_cache.insert(std::make_pair(t1, std::make_pair(exprt(),l)));

      return l;
    }    
    else
    {
      //      t1->interpolant_aig.add_variables(prop_conv.prop);
      literalt l = t1->interpolant_aig.convert(prop_conv.prop);
      literal_cache.insert(std::make_pair(t1, std::make_pair(exprt(),l)));

      return l;
    }    
  }
  else
  {
    literalt l1 = convert_as_it_is(prop_conv, t1->interpolant_left);
    literalt l2 = convert_as_it_is(prop_conv, t1->interpolant_right);

    literalt l34;
    
    if(t1->ntype == mixed_interpolantt::AND)
      l34 = prop_conv.prop.land(l1, l2);
    else
      l34 = prop_conv.prop.lor(l1, l2);
    literal_cache.insert(std::make_pair(t1, std::make_pair(exprt(), l34)));

    return l34;
  }  
  */
}

#if 0 
std::pair<exprt, literalt> interpolationt_word::start_instantiate_convert(
  prop_convt &prop_conv,
  const exprt &t1,
  const namespacet & ns)
{
  literalt l = instantiate_convert(prop_conv, t1, 0, ns);
  return std::make_pair(t1, l);
  /*
  if(t1->ntype == mixed_interpolantt::ROOT)
  {
    if(t1->expr)
    {

      std::map<mixed_interpolantt *, std::pair<exprt, literalt> > ::iterator it = literal_cache.find(t1);
      if(it != literal_cache.end())
	return std::make_pair(t1->interpolant_expr, (*it).second.second);

      literalt l = instantiate_convert(prop_conv, t1->interpolant_expr, 0, ns);
      literal_cache.insert(std::make_pair(t1, std::make_pair(t1->interpolant_expr, l)));

      return std::make_pair(t1->interpolant_expr, l);

    }
    else
    {
      aig_printt aig_print(t1->interpolant_aig, reverse_map);
      exprt e;
      aig_print(e);
      drop_timeframe(e);
      
      std::map<mixed_interpolantt *, std::pair<exprt, literalt> >::iterator it = literal_cache.find(t1);
      if(it != literal_cache.end())
	return std::make_pair(e, (*it).second.second);

      literalt l = instantiate_convert(prop_conv, e, 0, ns);
      literal_cache.insert(std::make_pair(t1, std::make_pair(e,l)));

      //HACK::we have not dropped the tf identifier yet.

      return std::make_pair(e,l);
    }
  }
  else
  {

    std::map<mixed_interpolantt *, std::pair<exprt, literalt> > ::iterator it = literal_cache.find(t1);
    if(it != literal_cache.end())
      {
	std::map<mixed_interpolantt *, std::pair<exprt, literalt> > ::iterator itl = literal_cache.find(t1->interpolant_left);    
	std::map<mixed_interpolantt *, std::pair<exprt, literalt> > ::iterator itr = literal_cache.find(t1->interpolant_right);
	//	std::cout << "found in lit cache\n";
	exprt e;
	if(t1->ntype == mixed_interpolantt::AND)
	  e = gen_and((*itl).second.first, (*itr).second.first);
	else
	  e = gen_or((*itl).second.first,(*itr).second.first);

	return std::make_pair(e, (*it).second.second);
      }

    std::pair<exprt, literalt> l1 = start_instantiate_convert(prop_conv, t1->interpolant_left, ns);
    std::pair<exprt, literalt> l2 = start_instantiate_convert(prop_conv, t1->interpolant_right, ns);

    exprt e;
    if(t1->ntype == mixed_interpolantt::AND)
      e = gen_and(l1.first, l2.first);
    else
      e = gen_or(l1.first, l2.first);


    literalt l = instantiate_convert(prop_conv, e, 0, ns);
    literal_cache.insert(std::make_pair(t1, std::make_pair(e, l)));
    return std::make_pair(e, l);
  }
  */
}

#endif
