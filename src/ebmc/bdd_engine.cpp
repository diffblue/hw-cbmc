/*******************************************************************\

Module: BDD Engine

Author: Daniel Kroening, daniel.kroening@inf.ethz.ch

\*******************************************************************/

#include <iostream>

#include "miniBDD/miniBDD.h"

#include <solvers/prop/aig_prop.h>
#include <solvers/sat/satcheck.h>
#include <trans-netlist/unwind_netlist.h>
#include <trans-netlist/trans_trace_netlist.h>
#include <trans-netlist/instantiate_netlist.h>

#include "ebmc_base.h"
#include "bdd_engine.h"

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
  bvt properties_nodes;
  
  miniBDD::mgr mgr;

  typedef miniBDD::BDD BDD;
  std::vector<BDD> constraints_BDDs, initial_BDDs,
                   transition_BDDs, properties_BDDs;
  
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
  void build_trans();
  
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
  
  void check_property(propertyt &, const BDD &);
  literalt convert_property(const propertyt &);
  
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
      
      status() << "Building netlist for properties" << eom;
      
      properties_nodes.reserve(properties.size());
      for(const propertyt &p : properties)
        properties_nodes.push_back(convert_property(p));
        
      status() << "Building BDD for netlist" << eom;
      
      allocate_vars(netlist.var_map);
      build_trans();
    }
    
    statistics() << "BDD nodes: "
                 << mgr.number_of_nodes() << eom;
    
    if(cmdline.isset("show-bdds"))
    {
      mgr.DumpTable(std::cout);
      std::cout << '\n';
      
      std::cout << "Properties:";
      for(const auto & l : properties_BDDs)
        std::cout << ' ' << l.node_number();
      std::cout << '\n';
        
      return 0;
    }

    if(properties.empty())
    {
      error() << "no properties" << eom;
      return 1;
    }

    unsigned p_nr=0;
    for(propertyt &p : properties)
    {
      check_property(p, properties_BDDs[p_nr]);
      p_nr++;
    }
    
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
      for(unsigned bit_nr=0; bit_nr<it.second.bits.size(); bit_nr++)
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

  ::unwind(netlist, bmc_map, *this, solver);
  ::unwind_property(bmc_map, properties_nodes[property.number],
                    property.timeframe_literals);
  
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

  namespacet ns(symbol_table);
  trans_tracet trans_trace;

  compute_trans_trace(
    property.timeframe_literals,
    bmc_map,
    solver,
    ns,
    property.counterexample);
}

/*******************************************************************\

Function: bdd_enginet::convert_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt bdd_enginet::convert_property(const propertyt &property)
{
  if(property.expr.is_true())
    return const_literal(true);
  else if(property.expr.is_false())
    return const_literal(false);
  else if(property.expr.id()==ID_AG ||
          property.expr.id()==ID_sva_always)
  {
    assert(property.expr.operands().size()==1);

    const exprt &p=property.expr.op0();

    aig_prop_constraintt aig_prop(netlist);
    aig_prop.set_message_handler(get_message_handler());
    
    const namespacet ns(symbol_table);
    
    return instantiate_convert(
      aig_prop, netlist.var_map, p, ns, get_message_handler());
  }
  else
  {
    error() << "unsupported property - only SVA always implemented"
            << messaget::eom;
    throw 0;
  }
}

/*******************************************************************\

Function: bdd_enginet::check_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bdd_enginet::check_property(
  propertyt &property,
  const BDD &p)
{
  if(property.is_disabled())
    return;

  status() << "Checking " << property.description << eom;
  property.status=propertyt::statust::UNKNOWN;

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

  statistics() << "Peak BDD nodes: "
               << peak_bdd_nodes << eom;
}

/*******************************************************************\

Function: bdd_enginet::build_trans

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bdd_enginet::build_trans()
{
  std::vector<BDD> BDDs;
  BDDs.resize(netlist.nodes.size());

  for(unsigned i=0; i<netlist.nodes.size(); i++)
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
    
  // properties
  for(literalt l : properties_nodes)
    properties_BDDs.push_back(aig2bdd(l, BDDs));
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

