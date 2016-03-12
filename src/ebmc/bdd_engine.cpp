/*******************************************************************\

Module: BDD Engine

Author: Daniel Kroening, daniel.kroening@inf.ethz.ch

\*******************************************************************/

#include <iostream>

#include <solvers/miniBDD/miniBDD.h>
#include <solvers/prop/aig_prop.h>
#include <solvers/sat/satcheck.h>

#include <trans-netlist/unwind_netlist.h>
#include <trans-netlist/trans_trace_netlist.h>
#include <trans-netlist/instantiate_netlist.h>

#include <langapi/language_util.h>

#include "ebmc_base.h"
#include "bdd_engine.h"
#include "negate_property.h"

/*******************************************************************\

   Class: bdd_enginet

 Purpose:

\*******************************************************************/

class bdd_enginet:public ebmc_baset
{
public:
  bdd_enginet(const cmdlinet &cmdline):ebmc_baset(cmdline)
  {
  }

  int operator()();

protected:
  netlistt netlist;

  // the Manager must appear before any BDDs
  // to do the cleanup in the right order
  miniBDD::mgr mgr;
  
  typedef miniBDD::BDD BDD;
  
  struct atomic_propositiont
  {
    literalt l;
    BDD bdd;
  };

  typedef std::map<exprt, atomic_propositiont> atomic_propositionst;
  atomic_propositionst atomic_propositions;
  
  std::vector<BDD> constraints_BDDs, initial_BDDs,
                   transition_BDDs;
  
  class vart
  {
  public:
    bool is_input;
    BDD current, next;
  };
  
  // this is our BDD variable ordering
  class ordering
  {
  public:
    bool operator()(const bv_varidt &a, const bv_varidt &b) const
    {
      if(a.bit_nr==b.bit_nr) return a.id<b.id;
      return a.bit_nr<b.bit_nr;
    }
  };
  
  typedef std::map<bv_varidt, vart, ordering> varst;
  varst vars;
  
  void allocate_vars(const var_mapt &);
  void build_BDDs();
  
  inline BDD aig2bdd(
    literalt l,
    const std::vector<BDD> &BDDs) const
  {
    if(l.is_true()) return mgr.True();
    if(l.is_false()) return mgr.False();
    assert(l.var_no()<BDDs.size());
    BDD result=BDDs[l.var_no()];
    if(l.sign()) result=!result;
    return result;
  }

  void get_atomic_propositions(const exprt &);  
  void check_property(propertyt &);
  BDD property2BDD(const exprt &);
  
  BDD current_to_next(const BDD &) const;
  BDD next_to_current(const BDD &) const;
  BDD project_next(const BDD &) const;
  BDD project_current(const BDD &) const;

  void compute_counterexample(
    propertyt &,
    unsigned number_of_timeframes);
};

/*******************************************************************\

Function: bdd_enginet::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int bdd_enginet::operator()()
{
  try
  {
    int result=get_model();
    if(result!=-1) return result;

    {  
      status() << "Building netlist" << eom;

      if(make_netlist(netlist))
      {
        error() << "Failed to build netlist" << eom;
        return 2;
      }
      
      status() << "Building netlist for atomic propositions" << eom;
      
      for(const propertyt &p : properties)
        get_atomic_propositions(p.expr);
        
      status() << "Building BDD for netlist" << eom;
      
      allocate_vars(netlist.var_map);
      build_BDDs();
    }
    
    statistics() << "BDD nodes: "
                 << mgr.number_of_nodes() << eom;
    
    if(cmdline.isset("show-bdds"))
    {
      mgr.DumpTable(std::cout);
      std::cout << '\n';
      
      std::cout << "Atomic propositions:\n";
      for(const auto & a : atomic_propositions)
      {
        std::string as_string=
          from_expr(namespacet(symbol_table), irep_idt(), a.first);
        std::cout << '`' << as_string << "' -> " << a.second.bdd.node_number();
      }

      std::cout << '\n';
        
      return 0;
    }

    if(properties.empty())
    {
      error() << "no properties" << eom;
      return 1;
    }

    for(propertyt &p : properties)
      check_property(p);
    
    report_results();

    // We return '0' if the property holds,
    // and '10' if it is violated.
    return property_failure()?10:0;
  }
  catch(const char *error_msg)
  {
    error() << error_msg << eom;
    return 1;
  }
  catch(int)
  {
    return 1;
  }
}

/*******************************************************************\

Function: bdd_enginet::allocate_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bdd_enginet::allocate_vars(const var_mapt &var_map)
{
  // gather variables according to variable ordering
  for(auto &it : var_map.map)
  {
    if(it.second.is_latch() ||
       it.second.is_input() ||
       it.second.is_nondet())
    {
      for(std::size_t bit_nr=0;
          bit_nr<it.second.bits.size();
          bit_nr++)
      {
        bv_varidt bv_varid(it.first, bit_nr);
        vars[bv_varid].is_input=
          it.second.is_input() || it.second.is_nondet();
      }
    }
  }
  
  // now allocate BBD variables
  for(auto &it : vars)
  {
    std::string s=it.first.as_string();
    it.second.current=mgr.Var(s);
    it.second.next=mgr.Var(s+"'");
  }
}

/*******************************************************************\

Function: bdd_enginet::current_to_next

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bdd_enginet::BDD bdd_enginet::current_to_next(const BDD &bdd) const
{
  BDD tmp=bdd;

  for(const auto &v : vars)
    tmp=substitute(tmp, v.second.current.var(), v.second.next);

  return tmp;
}

/*******************************************************************\

Function: bdd_enginet::next_to_current

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bdd_enginet::BDD bdd_enginet::next_to_current(const BDD &bdd) const
{
  BDD tmp=bdd;

  for(const auto &v : vars)
    tmp=substitute(tmp, v.second.next.var(), v.second.current);

  return tmp;
}

/*******************************************************************\

Function: bdd_enginet::project_next

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bdd_enginet::BDD bdd_enginet::project_next(const BDD &bdd) const
{
  BDD tmp=bdd;

  for(const auto &v : vars)
    tmp=exists(tmp, v.second.next.var());

  return tmp;
}

/*******************************************************************\

Function: bdd_enginet::project_current

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bdd_enginet::BDD bdd_enginet::project_current(const BDD &bdd) const
{
  BDD tmp=bdd;

  for(const auto &v : vars)
    tmp=exists(tmp, v.second.current.var());

  return tmp;
}

/*******************************************************************\

Function: bdd_enginet::compute_counterexample

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bdd_enginet::compute_counterexample(
  propertyt &property,
  unsigned number_of_timeframes)
{
  status() << "Computing counterexample with " << number_of_timeframes 
           << " timeframe(s)" << eom;

  bmc_mapt bmc_map;

  satcheckt solver;
  bmc_map.map_timeframes(netlist, number_of_timeframes, solver);
  
  const namespacet ns(symbol_table);

  ::unwind(netlist, bmc_map, *this, solver);
  ::unwind_property(property.expr, property.timeframe_literals,
                    get_message_handler(), solver, bmc_map, ns);
  
  // we need the propertyt to fail in one of the timeframes
  bvt clause=property.timeframe_literals;
  for(auto & l : clause) l=!l;
  solver.lcnf(clause);
  
  propt::resultt prop_result=
    solver.prop_solve();

  switch(prop_result)
  {
  case propt::P_SATISFIABLE: break; // this is what we want
  
  case propt::P_UNSATISFIABLE:
    throw "SAT solver says UNSAT!";
    
  default:
    throw "unexpected result from SAT solver";
  }

  trans_tracet trans_trace;

  compute_trans_trace(
    property.timeframe_literals,
    bmc_map,
    solver,
    ns,
    property.counterexample);
}

/*******************************************************************\

Function: bdd_enginet::check_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bdd_enginet::check_property(propertyt &property)
{
  if(property.is_disabled())
    return;

  status() << "Checking " << property.name << eom;
  property.status=propertyt::statust::UNKNOWN;

  // special treatment for always

  if(property.expr.id()==ID_AG ||
     property.expr.id()==ID_sva_always)
  {
    assert(property.expr.operands().size()==1);

    // recursive call
    const exprt &sub_expr=property.expr.op0();
    BDD p=property2BDD(sub_expr);

    // Start with !p, and go backwards until saturation or we hit an
    // initial state.
    
    BDD states=!p;
    unsigned iteration=0;
    
    for(const auto &c : constraints_BDDs)
      states = states & c;

    std::size_t peak_bdd_nodes=0;

    while(true)
    {
      iteration++;
      statistics() << "Iteration " << iteration << eom;

      // do we have an initial state?
      BDD intersection=states;
      
      for(const auto &i : initial_BDDs)
        intersection=intersection & i;

      peak_bdd_nodes=std::max(peak_bdd_nodes, mgr.number_of_nodes());

      if(!intersection.is_false())
      {
        property.make_failure();
        status() << "Property refuted" << eom;
        compute_counterexample(property, iteration);
        break;
      }
      
      // make the states be expressed in terms of 'next' variables
      BDD states_next=current_to_next(states);

      // now conjoin with transition relation
      BDD conjunction=states_next;
      
      for(const auto &t : transition_BDDs)
        conjunction = conjunction & t;
      
      for(const auto &c : constraints_BDDs)
        conjunction = conjunction & c;

      // now project away 'next' variables
      BDD pre_image=project_next(conjunction);
      
      // compute union
      BDD set_union=states | pre_image;

      // have we saturated?
      if((set_union==states).is_true())
      {
        property.make_success();
        status() << "Property holds" << eom;
        break;
      }

      states=set_union;

      peak_bdd_nodes=std::max(peak_bdd_nodes, mgr.number_of_nodes());
    }
  }
  else
  {
    // We check whether the BDD for the negation of the property
    // contains an initial state.
    exprt negation=negate_property(property.expr);
    BDD states=property2BDD(negation);

    // do we have an initial state?
    BDD intersection=states;
      
    for(const auto &i : initial_BDDs)
      intersection = intersection & i;

    for(const auto &c : constraints_BDDs)
      intersection = intersection & c;

    if(!intersection.is_false())
    {
      property.make_failure();
      status() << "Property refuted" << eom;
    }
    else
    {
      property.make_success();
      status() << "Property holds" << eom;
    }
  }
}

/*******************************************************************\

Function: bdd_enginet::property2BDD

  Inputs: a property expression

 Outputs: a BDD for a set of states

 Purpose: compute states that satisfy a particular property

\*******************************************************************/

bdd_enginet::BDD bdd_enginet::property2BDD(const exprt &expr)
{
  if(expr.is_true())
    return mgr.True();
  else if(expr.is_false())
    return mgr.False();
  else if(expr.id()==ID_not)
  {
    return !property2BDD(to_not_expr(expr).op());
  }
  else if(expr.id()==ID_implies ||
          expr.id()==ID_sva_overlapped_implication)
  {
    assert(expr.operands().size()==2);
    return !property2BDD(expr.op0()) | property2BDD(expr.op1());
  }
  else if(expr.id()==ID_and)
  {
    BDD result=mgr.True();
    for(const auto & op : expr.operands())
      result = result & property2BDD(op);
    return result;
  }
  else if(expr.id()==ID_or)
  {
    BDD result=mgr.False();
    for(const auto & op : expr.operands())
      result = result | property2BDD(op);
    return result;
  }
  else if(expr.id()==ID_sva_non_overlapped_implication)
  {
    assert(expr.operands().size()==2);
    
    // use sva_nexttime for this
    unary_predicate_exprt tmp(ID_sva_nexttime, expr.op1());
    return !property2BDD(expr.op0()) | property2BDD(tmp);
  }
  else if(expr.id()==ID_sva_nexttime)
  {
    assert(expr.operands().size()==1);

    // recursive call
    const exprt &sub_expr=expr.op0();
    BDD p=property2BDD(sub_expr);

    // make 'p' be expressed in terms of 'next' variables
    BDD p_next=current_to_next(p);

    // now conjoin with transition relation
    BDD conjunction=p_next;
    
    for(const auto &t : transition_BDDs)
      conjunction = conjunction & t;
    
    for(const auto &c : constraints_BDDs)
      conjunction = conjunction & c;

    // now project away 'next' variables
    BDD pre_image=project_next(conjunction);
        
    return pre_image;
  }
  else if(expr.id()==ID_sva_eventually)
  {
    assert(expr.operands().size()==1);

    // recursive call
    const exprt &sub_expr=expr.op0();
    BDD p=property2BDD(sub_expr);
    BDD states=p;
    
    while(true)
    {
      // make 'states' be expressed in terms of 'next' variables
      BDD states_next=current_to_next(p);

      // now conjoin with transition relation
      BDD conjunction=states_next;
      
      for(const auto &t : transition_BDDs)
        conjunction = conjunction & t;
      
      for(const auto &c : constraints_BDDs)
        conjunction = conjunction & c;

      // now project away 'next' variables
      BDD pre_image=project_next(conjunction);
      
      // compute intersection
      BDD set_intersection=states & pre_image;

      // have we saturated?
      if((set_intersection==states).is_true())
        break;

      states=set_intersection;
    }
    
    return states;
  }
  else if(expr.id()==ID_AG ||
          expr.id()==ID_sva_always)
  {
    assert(expr.operands().size()==1);

    // recursive call
    const exprt &sub_expr=expr.op0();
    BDD p=property2BDD(sub_expr);
    BDD states=p;
    
    while(true)
    {
      // make 'states' be expressed in terms of 'next' variables
      BDD states_next=current_to_next(p);

      // now conjoin with transition relation
      BDD conjunction=states_next;
      
      for(const auto &t : transition_BDDs)
        conjunction = conjunction & t;
      
      for(const auto &c : constraints_BDDs)
        conjunction = conjunction & c;

      // now project away 'next' variables
      BDD pre_image=project_next(conjunction);
      
      // compute union
      BDD set_union=states | pre_image;

      // have we saturated?
      if((set_union==states).is_true())
        break;

      states=set_union;
    }
    
    return states;
  }
  else
  {
    atomic_propositionst::const_iterator it=
      atomic_propositions.find(expr);
    
    if(it!=atomic_propositions.end())
      return it->second.bdd;
  }

  error() << "unsupported property -- `" << expr.id()
          << "' not implemented" << messaget::eom;
  throw 0;
}

/*******************************************************************\

Function: bdd_enginet::get_atomic_propositions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bdd_enginet::get_atomic_propositions(const exprt &expr)
{
  if(expr.id()==ID_and ||
     expr.id()==ID_or ||
     expr.id()==ID_not ||
     expr.id()==ID_implies ||
     expr.id()==ID_AG ||
     expr.id()==ID_sva_always ||
     expr.id()==ID_sva_overlapped_implication ||
     expr.id()==ID_sva_non_overlapped_implication ||
     expr.id()==ID_sva_nexttime ||
     expr.id()==ID_sva_eventually ||
     expr.id()==ID_sva_until ||
     expr.id()==ID_sva_s_until ||
     expr.id()==ID_sva_until_with ||
     expr.id()==ID_sva_s_until_with)
  {
    for(const auto & op : expr.operands())
      get_atomic_propositions(op);
  }
  else
  {
    // do we have it already?  
    if(atomic_propositions.find(expr)!=
       atomic_propositions.end())
      return; // yes
  
    assert(expr.type().id()==ID_bool);

    aig_prop_constraintt aig_prop(netlist);
    aig_prop.set_message_handler(get_message_handler());
    
    const namespacet ns(symbol_table);
    
    literalt l=instantiate_convert(
      aig_prop, netlist.var_map, expr, ns, get_message_handler());
    
    atomic_propositiont &a=atomic_propositions[expr];
    
    a.l=l;
    a.bdd=mgr.False();
  }
}

/*******************************************************************\

Function: bdd_enginet::build_BDDs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bdd_enginet::build_BDDs()
{
  std::vector<BDD> BDDs;
  BDDs.resize(netlist.nodes.size());

  for(std::size_t i=0; i<netlist.nodes.size(); i++)
  {
    const netlistt::nodet &n=netlist.nodes[i];
  
    // A node is either an 'and' or a variable/nondet
    if(n.is_and())
    {
      BDD a=aig2bdd(n.a, BDDs);
      BDD b=aig2bdd(n.b, BDDs);
    
      BDDs[i]=a & b;
    }
    else // current-state variable or nondet
    {
      bv_varidt id=netlist.var_map.reverse(i);
      varst::const_iterator it=vars.find(id);
      assert(it!=vars.end());
      BDDs[i]=it->second.current;
    }
  }
  
  // Add the next-state variable constraints for
  // the state-holding elements.
  for(const auto &v : vars)
    if(!v.second.is_input)
    {
      literalt next=netlist.var_map.get_next(v.first);
      transition_BDDs.push_back(aig2bdd(next, BDDs)==v.second.next);
    }
  
  // general AIG conditions
  for(literalt l : netlist.constraints)
    constraints_BDDs.push_back(aig2bdd(l, BDDs));
    
  // initial state conditions
  for(literalt l : netlist.initial)
    initial_BDDs.push_back(aig2bdd(l, BDDs));
    
  // transition conditions
  for(literalt l : netlist.transition)
    transition_BDDs.push_back(aig2bdd(l, BDDs));

  // atomic propositions
  for(auto & p : atomic_propositions)
    p.second.bdd=aig2bdd(p.second.l, BDDs);
}

/*******************************************************************\

Function: do_bdd

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int do_bdd(const cmdlinet &cmdline)
{
  return bdd_enginet(cmdline)();
}

