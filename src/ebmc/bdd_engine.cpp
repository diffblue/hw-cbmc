/*******************************************************************\

Module: BDD Engine

Author: Daniel Kroening, daniel.kroening@inf.ethz.ch

\*******************************************************************/

#include "bdd_engine.h"

#include <util/expr_util.h>
#include <util/format_expr.h>

#include <solvers/bdd/miniBDD/miniBDD.h>
#include <solvers/sat/satcheck.h>
#include <temporal-logic/negate_property.h>
#include <temporal-logic/temporal_expr.h>
#include <temporal-logic/temporal_logic.h>
#include <trans-netlist/aig_prop.h>
#include <trans-netlist/instantiate_netlist.h>
#include <trans-netlist/trans_to_netlist.h>
#include <trans-netlist/trans_trace_netlist.h>
#include <trans-netlist/unwind_netlist.h>
#include <verilog/sva_expr.h>

#include <algorithm>
#include <iostream>

/*******************************************************************\

   Class: bdd_enginet

 Purpose:

\*******************************************************************/

class bdd_enginet
{
public:
  bdd_enginet(
    const cmdlinet &_cmdline,
    transition_systemt &_transition_system,
    ebmc_propertiest &_properties,
    message_handlert &_message_handler)
    : cmdline(_cmdline),
      transition_system(_transition_system),
      properties(_properties),
      message(_message_handler),
      ns(transition_system.symbol_table)
  {
  }

  property_checker_resultt operator()();

protected:
  using propertiest = ebmc_propertiest;
  using propertyt = ebmc_propertiest::propertyt;
  const cmdlinet &cmdline;
  transition_systemt &transition_system;
  propertiest &properties;
  messaget message;
  const namespacet ns;
  netlistt netlist;

  // the Manager must appear before any BDDs
  // to do the cleanup in the right order
  mini_bdd_mgrt mgr;
  
  typedef mini_bddt BDD;
  
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
    assert(result.is_initialized());
    if(l.sign()) result=!result;
    return result;
  }

  void get_atomic_propositions(const exprt &);
  void check_property(propertyt &);

  BDD current_to_next(const BDD &) const;
  BDD next_to_current(const BDD &) const;
  BDD project_next(const BDD &) const;
  BDD project_current(const BDD &) const;

  void compute_counterexample(
    propertyt &,
    unsigned number_of_timeframes);

  void check_AGp(propertyt &);
  void check_CTL(propertyt &);
  BDD CTL(const exprt &);
  BDD EX(BDD);
  BDD AX(BDD f)
  {
    return !EX(!f);
  }
  BDD EF(BDD);
  BDD AF(BDD f)
  {
    return !EG(!f);
  }
  BDD EG(BDD);
  BDD AG(BDD f)
  {
    return !EF(!f);
  }
  BDD EU(BDD, BDD);
  BDD AU(BDD, BDD);
  BDD ER(BDD f1, BDD f2)
  {
    return !AU(!f1, !f2);
  }
  BDD AR(BDD f1, BDD f2)
  {
    return !EU(!f1, !f2);
  }
  BDD fixedpoint(std::function<BDD(BDD)>, BDD);
};

/*******************************************************************\

Function: bdd_enginet::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

property_checker_resultt bdd_enginet::operator()()
{
  try
  {
    for(auto &property : properties.properties)
    {
      // no support for $past
      if(has_subexpr(property.normalized_expr, ID_verilog_past))
        property.failure("property not supported by BDD engine");
    }

    // any properties left?
    if(!properties.has_unknown_property())
      return property_checker_resultt::VERIFICATION_RESULT;

    const auto property_map = properties.make_property_map();

    message.status() << "Building netlist" << messaget::eom;

    convert_trans_to_netlist(
      transition_system.symbol_table,
      transition_system.main_symbol->name,
      property_map,
      netlist,
      message.get_message_handler());

    message.statistics() << "Latches: " << netlist.var_map.latches.size()
                         << ", nodes: " << netlist.number_of_nodes()
                         << messaget::eom;

    for(const auto &[_, expr] : property_map)
      get_atomic_propositions(expr);

    message.status() << "Building BDD for netlist" << messaget::eom;

    allocate_vars(netlist.var_map);
    build_BDDs();

    message.statistics() << "BDD nodes: " << mgr.number_of_nodes()
                         << messaget::eom;

    if(cmdline.isset("show-bdds"))
    {
      mgr.DumpTable(std::cout);
      std::cout << '\n';
      
      std::cout << "Atomic propositions:\n";
      for(const auto & a : atomic_propositions)
      {
        std::cout << '`' << format(a.first) << "' -> "
                  << a.second.bdd.node_number() << '\n';
      }

      std::cout << '\n';

      return property_checker_resultt::SUCCESS;
    }

    if(properties.properties.empty())
    {
      message.error() << "no properties" << messaget::eom;
      return property_checker_resultt::ERROR;
    }

    for(propertyt &p : properties.properties)
      check_property(p);

    return property_checker_resultt::VERIFICATION_RESULT;
  }
  catch(const char *error_msg)
  {
    message.error() << error_msg << messaget::eom;
    return property_checker_resultt::ERROR;
  }
  catch(int)
  {
    return property_checker_resultt::ERROR;
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
  // Supported by BMC engine?
  if(!netlist_bmc_supports_property(property.normalized_expr))
    return;

  message.status() << "Computing counterexample with " << number_of_timeframes
                   << " timeframe(s)" << messaget::eom;

  satcheckt solver{message.get_message_handler()};
  const auto bmc_map = bmc_mapt{netlist, number_of_timeframes, solver};

  ::unwind(netlist, bmc_map, message, solver);

  // find the netlist property
  auto netlist_property = netlist.properties.find(property.identifier);
  CHECK_RETURN(netlist_property != netlist.properties.end());

  ::unwind_property(
    netlist_property->second, bmc_map, property.timeframe_literals);

  // we need the propertyt to fail in one of the timeframes
  bvt clause=property.timeframe_literals;
  for(auto & l : clause) l=!l;
  solver.lcnf(clause);
  
  propt::resultt prop_result=
    solver.prop_solve();

  switch(prop_result)
  {
  case propt::resultt::P_SATISFIABLE: break; // this is what we want
  
  case propt::resultt::P_UNSATISFIABLE:
    throw "SAT solver says UNSAT!";
  case propt::resultt::P_ERROR:
  default:
    throw "unexpected result from SAT solver";
  }

  property.witness_trace =
    compute_trans_trace(property.timeframe_literals, bmc_map, solver, ns);
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

  if(property.is_assumed())
    return;

  message.status() << "Checking " << property.name << messaget::eom;
  property.status=propertyt::statust::UNKNOWN;

  // special treatment for AGp
  auto is_AGp = [](const exprt &expr) {
    return (expr.id() == ID_AG || expr.id() == ID_G ||
            expr.id() == ID_sva_always) &&
           !has_temporal_operator(to_unary_expr(expr).op());
  };

  // Our engine knows CTL only.
  // We map selected path properties to CTL.

  if(
    property.normalized_expr.id() == ID_G &&
    to_G_expr(property.normalized_expr).op().id() == ID_F &&
    !has_temporal_operator(
      to_F_expr(to_G_expr(property.normalized_expr).op()).op()))
  {
    // G F p --> AG AF p
    auto p = to_F_expr(to_G_expr(property.normalized_expr).op()).op();
    property.normalized_expr = AG_exprt{AF_exprt{p}};
  }

  if(
    property.normalized_expr.id() == ID_sva_always &&
    to_sva_always_expr(property.normalized_expr).op().id() ==
      ID_sva_s_eventually &&
    !has_temporal_operator(to_sva_s_eventually_expr(
                             to_sva_always_expr(property.normalized_expr).op())
                             .op()))
  {
    // always s_eventually p --> AG AF p
    auto p = to_sva_s_eventually_expr(
               to_sva_always_expr(property.normalized_expr).op())
               .op();
    property.normalized_expr = AG_exprt{AF_exprt{p}};
  }

  if(is_AGp(property.normalized_expr))
  {
    check_AGp(property);
  }
  else if(is_CTL(property.normalized_expr))
  {
    check_CTL(property);
  }
  else
    property.failure("property not supported by BDD engine");
}

/*******************************************************************\

Function: bdd_enginet::check_AGp

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bdd_enginet::check_AGp(propertyt &property)
{
  const exprt &sub_expr = to_unary_expr(property.normalized_expr).op();
  BDD p = CTL(sub_expr);

  // Start with !p, and go backwards until saturation or we hit an
  // initial state.

  BDD states = !p;
  unsigned iteration = 0;

  for(const auto &c : constraints_BDDs)
    states = states & c;

  std::size_t peak_bdd_nodes = 0;

  while(true)
  {
    iteration++;
    message.statistics() << "Iteration " << iteration << messaget::eom;

    // do we have an initial state?
    BDD intersection = states;

    for(const auto &i : initial_BDDs)
      intersection = intersection & i;

    peak_bdd_nodes = std::max(peak_bdd_nodes, mgr.number_of_nodes());

    if(!intersection.is_false())
    {
      property.refuted();
      message.status() << "Property refuted" << messaget::eom;
      compute_counterexample(property, iteration);
      break;
    }

    // make the states be expressed in terms of 'next' variables
    BDD states_next = current_to_next(states);

    // now conjoin with transition relation
    BDD conjunction = states_next;

    for(const auto &t : transition_BDDs)
      conjunction = conjunction & t;

    for(const auto &c : constraints_BDDs)
      conjunction = conjunction & c;

    // now project away 'next' variables
    BDD pre_image = project_next(conjunction);

    // compute union
    BDD set_union = states | pre_image;

    // have we saturated?
    if((set_union == states).is_true())
    {
      property.proved();
      message.status() << "Property proved" << messaget::eom;
      break;
    }

    states = set_union;

    peak_bdd_nodes = std::max(peak_bdd_nodes, mgr.number_of_nodes());
  }
}

/*******************************************************************\

Function: bdd_enginet::check_CTL

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bdd_enginet::check_CTL(propertyt &property)
{
  // For a CTL formula f, calculate the set of states that satisfy
  // !f, and then check if that contains any initial state.
  BDD not_f = !CTL(property.normalized_expr);

  BDD intersection = not_f;

  for(const auto &i : initial_BDDs)
    intersection = intersection & i;

  for(const auto &c : constraints_BDDs)
    intersection = intersection & c;

  if(intersection.is_false())
  {
    // intersection empty, proved
    property.proved();
    message.status() << "Property proved" << messaget::eom;
  }
  else
  {
    // refuted
    property.refuted();
    message.status() << "Property refuted" << messaget::eom;
  }
}

/*******************************************************************\

Function: bdd_enginet::CTL

  Inputs: a CTL expression

 Outputs: a BDD for the set of states that satisfies the expression

 Purpose: compute states that satisfy a particular property

\*******************************************************************/

bdd_enginet::BDD bdd_enginet::CTL(const exprt &expr)
{
  if(expr.is_true())
    return mgr.True();
  else if(expr.is_false())
    return mgr.False();
  else if(expr.id()==ID_not)
  {
    return !CTL(to_not_expr(expr).op());
  }
  else if(expr.id() == ID_implies)
  {
    return (!CTL(to_binary_expr(expr).lhs())) | CTL(to_binary_expr(expr).rhs());
  }
  else if(expr.id()==ID_and)
  {
    BDD result=mgr.True();
    for(const auto & op : expr.operands())
      result = result & CTL(op);
    return result;
  }
  else if(expr.id()==ID_or)
  {
    BDD result=mgr.False();
    for(const auto & op : expr.operands())
      result = result | CTL(op);
    return result;
  }
  else if(
    expr.id() == ID_equal && to_equal_expr(expr).lhs().type().id() == ID_bool)
  {
    return (
      !(CTL(to_binary_expr(expr).lhs())) ^ CTL(to_binary_expr(expr).rhs()));
  }
  else if(expr.id() == ID_EX)
  {
    return EX(CTL(to_EX_expr(expr).op()));
  }
  else if(expr.id() == ID_EF)
  {
    return EF(CTL(to_EF_expr(expr).op()));
  }
  else if(expr.id() == ID_EG)
  {
    return EG(CTL(to_EG_expr(expr).op()));
  }
  else if(expr.id() == ID_AX)
  {
    return AX(CTL(to_AX_expr(expr).op()));
  }
  else if(expr.id() == ID_AF)
  {
    return AF(CTL(to_AF_expr(expr).op()));
  }
  else if(expr.id() == ID_AG)
  {
    return AG(CTL(to_AG_expr(expr).op()));
  }
  else if(expr.id() == ID_EU)
  {
    auto &EU_expr = to_EU_expr(expr);
    return EU(CTL(EU_expr.lhs()), CTL(EU_expr.rhs()));
  }
  else if(expr.id() == ID_AU)
  {
    auto &AU_expr = to_AU_expr(expr);
    return AU(CTL(AU_expr.lhs()), CTL(AU_expr.rhs()));
  }
  else if(expr.id() == ID_ER)
  {
    auto &ER_expr = to_ER_expr(expr);
    return ER(CTL(ER_expr.lhs()), CTL(ER_expr.rhs()));
  }
  else if(expr.id() == ID_AR)
  {
    auto &AR_expr = to_AR_expr(expr);
    return AR(CTL(AR_expr.lhs()), CTL(AR_expr.rhs()));
  }
  else
  {
    atomic_propositionst::const_iterator it=
      atomic_propositions.find(expr);
    
    if(it!=atomic_propositions.end())
      return it->second.bdd;
  }

  message.error() << "unsupported property -- `" << expr.id()
                  << "' not implemented" << messaget::eom;
  throw 0;
}

/*******************************************************************\

Function: bdd_enginet::EX

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bdd_enginet::BDD bdd_enginet::EX(BDD f)
{
  for(const auto &c : constraints_BDDs)
    f = f & c;

  // make 'f' be expressed in terms of 'next' variables
  BDD p_next = current_to_next(f);

  // now conjoin with transition relation
  BDD conjunction = p_next;

  for(const auto &t : transition_BDDs)
    conjunction = conjunction & t;

  for(const auto &c : constraints_BDDs)
    conjunction = conjunction & c;

  // now project away 'next' variables
  BDD pre_image = project_next(conjunction);

  return pre_image;
}

/*******************************************************************\

Function: bdd_enginet::fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bdd_enginet::BDD bdd_enginet::fixedpoint(std::function<BDD(BDD)> tau, BDD x)
{
  // Apply tau(x) until saturation.
  while(true)
  {
    BDD image = tau(x);

    // fixpoint?
    if((image == x).is_true())
      return x; // done

    x = image;
  }
}

/*******************************************************************\

Function: bdd_enginet::EG

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bdd_enginet::BDD bdd_enginet::EG(BDD f)
{
  // EG f = f ∧ EX EG f
  // Iterate x ∧ EX x until saturation.
  auto tau = [this](BDD x) { return x & EX(x); };

  return fixedpoint(tau, f);
}

/*******************************************************************\

Function: bdd_enginet::EF

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bdd_enginet::BDD bdd_enginet::EF(BDD f)
{
  // EF f ↔ f ∨ EX EF f
  // Iterate x ∨ EX x until saturation.
  auto tau = [this](BDD x) { return x | EX(x); };

  return fixedpoint(tau, f);
}

/*******************************************************************\

Function: bdd_enginet::EU

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bdd_enginet::BDD bdd_enginet::EU(BDD f1, BDD f2)
{
  // Iterate x ∨ f2 ∨ (f1 ∧ EX x) until saturation
  auto tau = [this, f1, f2](BDD x) { return x | f2 | (f1 & EX(x)); };

  return fixedpoint(tau, mgr.False());
}

/*******************************************************************\

Function: bdd_enginet::AU

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bdd_enginet::BDD bdd_enginet::AU(BDD f1, BDD f2)
{
  // Iterate x ∨ f2 ∨ (f1 ∧ AX x) until saturation
  auto tau = [this, f1, f2](BDD x) { return x | f2 | (f1 & AX(x)); };

  return fixedpoint(tau, mgr.False());
}

/*******************************************************************\

Function: bdd_enginet::get_atomic_propositions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bdd_enginet::get_atomic_propositions(const exprt &expr)
{
  if(
    expr.id() == ID_and || expr.id() == ID_or || expr.id() == ID_not ||
    expr.id() == ID_implies ||
    (expr.id() == ID_equal &&
     to_equal_expr(expr).lhs().type().id() == ID_bool) ||
    is_temporal_operator(expr))
  {
    for(const auto & op : expr.operands())
      if(op.type().id() == ID_bool)
        get_atomic_propositions(op);
  }
  else
  {
    // do we have it already?  
    if(atomic_propositions.find(expr)!=
       atomic_propositions.end())
      return; // yes
  
    assert(expr.type().id()==ID_bool);

    aig_prop_constraintt aig_prop(netlist, message.get_message_handler());

    literalt l = instantiate_convert(
      aig_prop, netlist.var_map, expr, ns, message.get_message_handler());

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

  // assumptions
  for(auto &property : properties.properties)
    if(property.is_assumed())
    {
      // We currently only do sva_always assumptions.
      auto &expr = property.normalized_expr;
      if(
        expr.id() == ID_sva_always &&
        !has_temporal_operator(to_unary_expr(expr).op()))
      {
        // find the netlist property
        auto netlist_property = netlist.properties.find(property.identifier);
        CHECK_RETURN(netlist_property != netlist.properties.end());
        auto l = std::get<netlistt::Gpt>(netlist_property->second).p;
        constraints_BDDs.push_back(aig2bdd(l, BDDs));
      }
    }
}

/*******************************************************************\

Function: bdd_engine

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

property_checker_resultt bdd_engine(
  const cmdlinet &cmdline,
  transition_systemt &transition_system,
  ebmc_propertiest &properties,
  message_handlert &message_handler)
{
  return bdd_enginet{cmdline, transition_system, properties, message_handler}();
}

