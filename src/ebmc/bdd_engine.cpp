/*******************************************************************\

Module: BDD Engine

Author: Daniel Kroening, daniel.kroening@inf.ethz.ch

\*******************************************************************/

#include "bdd_engine.h"

#include <util/expr_util.h>
#include <util/format_expr.h>

#include <ebmc/liveness_to_safety.h>
#include <ebmc/transition_system.h>
#include <solvers/bdd/miniBDD/miniBDD.h>
#include <solvers/prop/literal_expr.h>
#include <solvers/sat/satcheck.h>
#include <temporal-logic/ctl.h>
#include <temporal-logic/ltl.h>
#include <temporal-logic/sva_to_ltl.h>
#include <temporal-logic/temporal_logic.h>
#include <trans-netlist/aig_prop.h>
#include <trans-netlist/instantiate_netlist.h>
#include <trans-netlist/trans_trace_netlist.h>
#include <trans-netlist/unwind_netlist.h>

#include "bdd_model_checker.h"
#include "netlist.h"

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

  static std::optional<exprt> property_supported(const exprt &);

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

  std::vector<BDD> initial_BDDs;

  bdd_transition_relationt transition_relation;

  class vart
  {
  public:
    bool is_input;
    BDD current_bdd, next_bdd;
    literalt current_aig;
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

  void compute_counterexample(
    propertyt &,
    unsigned number_of_timeframes);

  void check_AGp(propertyt &);
  void check_CTL(propertyt &);
  BDD CTL(const exprt &, bdd_model_checkert &);
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
    // any properties left?
    if(!properties.has_unfinished_property())
      return property_checker_resultt{properties};

    // possibly apply liveness-to-safety
    if(cmdline.isset("liveness-to-safety"))
      liveness_to_safety(transition_system, properties);

    message.status() << "Building netlist" << messaget::eom;

    netlist = make_netlist(
      transition_system, properties, cmdline, message.get_message_handler());

    message.statistics() << "Latches: " << netlist.var_map.latches.size()
                         << ", nodes: " << netlist.number_of_nodes()
                         << messaget::eom;

    for(auto &property : properties.properties)
    {
      if(!property.is_disabled() && !property.is_assumed())
      {
        auto converted_opt = property_supported(property.normalized_expr);
        if(converted_opt.has_value())
        {
          property.normalized_expr = *converted_opt;
          get_atomic_propositions(*converted_opt);
        }
        else
          property.failure("property not supported by BDD engine");
      }
    }

    message.status() << "Building BDD for netlist" << messaget::eom;

    allocate_vars(netlist.var_map);
    build_BDDs();

    message.statistics() << "BDD nodes: " << mgr.number_of_nodes()
                         << messaget::eom;

    if(cmdline.isset("show-bdds"))
    {
      mgr.DumpTable(std::cout);
      std::cout << '\n';

      std::cout << "Variables:\n";
      for(const auto &[id, var] : vars)
      {
        std::cout << id << " <-> " << cubes(var.current_bdd);
        std::cout << "next(" << id << ") <-> " << cubes(var.next_bdd);
      }
      std::cout << '\n';

      std::cout << "Initial states:\n";
      for(const auto &bdd : initial_BDDs)
        std::cout << cubes(bdd) << '\n';

      std::cout << "In-state constraints:\n";
      for(const auto &bdd : transition_relation.constraint_conjuncts)
        std::cout << cubes(bdd) << '\n';

      std::cout << "Transition relation:\n";
      for(const auto &bdd : transition_relation.transition_conjuncts)
        std::cout << cubes(bdd) << '\n';

      std::cout << "Atomic propositions:\n";
      for(const auto &a : atomic_propositions)
        std::cout << '`' << format(a.first) << "':\n"
                  << cubes(a.second.bdd) << '\n';

      bdd_model_checkert model_checker(transition_relation);

      std::cout << "Properties:\n";
      for(const auto &property : properties.properties)
      {
        if(
          property.is_disabled() || property.is_assumed() ||
          property.is_failure())
        {
        }
        else
        {
          auto result = CTL(property.normalized_expr, model_checker);
          std::cout << property.name << ":\n" << cubes(result) << '\n';
        }
      }

      return property_checker_resultt::success();
    }

    if(properties.properties.empty())
    {
      message.error() << "no properties" << messaget::eom;
      return property_checker_resultt::error();
    }

    for(propertyt &p : properties.properties)
      check_property(p);

    return property_checker_resultt{properties};
  }
  catch(const char *error_msg)
  {
    message.error() << error_msg << messaget::eom;
    return property_checker_resultt::error();
  }
  catch(int)
  {
    return property_checker_resultt::error();
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
        bv_varidt bv_varid{it.first, bit_nr};
        auto &var = vars[bv_varid];
        var.is_input = it.second.is_input() || it.second.is_nondet();
        var.current_aig = it.second.bits[bit_nr].current;
      }
    }
  }
  
  // now allocate BBD variables
  for(auto &it : vars)
  {
    std::string s=it.first.as_string();
    it.second.current_bdd = mgr.Var(s);
    it.second.next_bdd = mgr.Var(s + "'");
  }
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

  property.timeframe_literals =
    ::unwind_property(netlist_property->second.value(), bmc_map);

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

Function: bdd_enginet::property_supported

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::optional<exprt> bdd_enginet::property_supported(const exprt &expr)
{
  // Our engine knows all of CTL.
  if(is_CTL(expr))
    return expr;

  if(is_LTL(expr))
  {
    // We can map selected path properties to CTL.
    return LTL_to_CTL(expr);
  }

  if(is_SVA(expr))
  {
    // We can map some SVA to LTL. In turn, some of that can be mapped to CTL.
    try
    {
      auto ltl = SVA_to_LTL(expr);
      return property_supported(ltl);
    }
    catch(sva_to_ltl_unsupportedt)
    {
      return {};
    }
  }

  return {};
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

  if(property.is_failure())
    return;

  message.status() << "Checking " << property.name << messaget::eom;
  property.status=propertyt::statust::UNKNOWN;

  if(is_AGp(property.normalized_expr))
  {
    check_AGp(property);
  }
  else if(is_CTL(property.normalized_expr))
  {
    check_CTL(property);
  }
  else
    DATA_INVARIANT(false, "unexpected normalized property");
}

/*******************************************************************\

Function: bdd_enginet::check_AGp

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bdd_enginet::check_AGp(propertyt &property)
{
  bdd_model_checkert model_checker(transition_relation);

  const exprt &sub_expr = to_unary_expr(property.normalized_expr).op();
  BDD p = CTL(sub_expr, model_checker);

  // Start with !p, and go backwards until saturation or we hit an
  // initial state.

  BDD states = !p;
  unsigned iteration = 0;

  for(const auto &c : transition_relation.constraint_conjuncts)
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
      if(property.is_exists_path())
      {
        property.proved("BDD");
        message.status() << "Path-exists property proved" << messaget::eom;
      }
      else
      {
        property.refuted("BDD");
        message.status() << "Property refuted" << messaget::eom;
      }
      compute_counterexample(property, iteration);
      break;
    }

    // EX(states) gives us the pre-image
    BDD pre_image = model_checker.EX(states);

    // compute union
    BDD set_union = states | pre_image;

    // have we saturated?
    if((set_union == states).is_true())
    {
      if(property.is_exists_path())
      {
        property.refuted("BDD");
        message.status() << "Path-exists property refuted" << messaget::eom;
      }
      else
      {
        property.proved("BDD");
        message.status() << "Property proved" << messaget::eom;
      }
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
  bdd_model_checkert model_checker(transition_relation);

  // For a CTL formula f, calculate the set of states that satisfy
  // !f, and then check if that contains any initial state.
  BDD not_f = !CTL(property.normalized_expr, model_checker);

  BDD intersection = not_f;

  for(const auto &i : initial_BDDs)
    intersection = intersection & i;

  for(const auto &c : transition_relation.constraint_conjuncts)
    intersection = intersection & c;

  if(intersection.is_false())
  {
    // intersection empty, proved
    property.proved("BDD");
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

bdd_enginet::BDD bdd_enginet::CTL(const exprt &expr, bdd_model_checkert &mc)
{
  if(expr.is_true())
    return mgr.True();
  else if(expr.is_false())
    return mgr.False();
  else if(expr.id()==ID_not)
  {
    return !CTL(to_not_expr(expr).op(), mc);
  }
  else if(expr.id() == ID_implies)
  {
    return (!CTL(to_binary_expr(expr).lhs(), mc)) |
           CTL(to_binary_expr(expr).rhs(), mc);
  }
  else if(expr.id()==ID_and)
  {
    BDD result=mgr.True();
    for(const auto & op : expr.operands())
      result = result & CTL(op, mc);
    return result;
  }
  else if(expr.id()==ID_or)
  {
    BDD result=mgr.False();
    for(const auto & op : expr.operands())
      result = result | CTL(op, mc);
    return result;
  }
  else if(
    expr.id() == ID_equal && to_equal_expr(expr).lhs().type().id() == ID_bool)
  {
    return (
      !(CTL(to_binary_expr(expr).lhs(), mc)) ^
      CTL(to_binary_expr(expr).rhs(), mc));
  }
  else if(expr.id() == ID_EX)
  {
    return mc.EX(CTL(to_EX_expr(expr).op(), mc));
  }
  else if(expr.id() == ID_EF)
  {
    return mc.EF(CTL(to_EF_expr(expr).op(), mc));
  }
  else if(expr.id() == ID_EG)
  {
    return mc.EG(CTL(to_EG_expr(expr).op(), mc));
  }
  else if(expr.id() == ID_AX)
  {
    return mc.AX(CTL(to_AX_expr(expr).op(), mc));
  }
  else if(expr.id() == ID_AF)
  {
    return mc.AF(CTL(to_AF_expr(expr).op(), mc));
  }
  else if(expr.id() == ID_AG)
  {
    return mc.AG(CTL(to_AG_expr(expr).op(), mc));
  }
  else if(expr.id() == ID_EU)
  {
    auto &EU_expr = to_EU_expr(expr);
    return mc.EU(CTL(EU_expr.lhs(), mc), CTL(EU_expr.rhs(), mc));
  }
  else if(expr.id() == ID_AU)
  {
    auto &AU_expr = to_AU_expr(expr);
    return mc.AU(CTL(AU_expr.lhs(), mc), CTL(AU_expr.rhs(), mc));
  }
  else if(expr.id() == ID_ER)
  {
    auto &ER_expr = to_ER_expr(expr);
    return mc.ER(CTL(ER_expr.lhs(), mc), CTL(ER_expr.rhs(), mc));
  }
  else if(expr.id() == ID_AR)
  {
    auto &AR_expr = to_AR_expr(expr);
    return mc.AR(CTL(AR_expr.lhs(), mc), CTL(AR_expr.rhs(), mc));
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
  std::vector<BDD> BDDs(netlist.nodes.size());

  // attach the current-state BDDs to their AIG nodes
  for(const auto &[_, var] : vars)
  {
    auto l = var.current_aig;
    BDD result = var.current_bdd;
    if(l.sign())
      result = !result;
    DATA_INVARIANT(l.var_no() < BDDs.size(), "AIG node in range");
    BDDs[l.var_no()] = result;
  }

  for(std::size_t i=0; i<netlist.nodes.size(); i++)
  {
    const netlistt::nodet &n=netlist.nodes[i];
  
    // A node is either an 'and' or a variable/nondet
    if(n.is_and())
    {
      // This relies on the dependency ordering of the AIG
      BDD a=aig2bdd(n.a, BDDs);
      BDD b=aig2bdd(n.b, BDDs);
    
      BDDs[i]=a & b;
    }
    else
    {
      // already done above
      DATA_INVARIANT(BDDs[i].is_initialized(), "non-AND BDD already done");
    }
  }

  // populate the transition relation variable pairs
  for(const auto &v : vars)
  {
    transition_relation.variables.push_back(
      {v.second.current_bdd, v.second.next_bdd});
  }

  // Add the next-state variable constraints for
  // the state-holding elements.
  for(const auto &v : vars)
    if(!v.second.is_input)
    {
      literalt next=netlist.var_map.get_next(v.first);
      transition_relation.transition_conjuncts.push_back(
        aig2bdd(next, BDDs) == v.second.next_bdd);
    }
  
  // general AIG conditions
  for(literalt l : netlist.constraints)
    transition_relation.constraint_conjuncts.push_back(aig2bdd(l, BDDs));

  // initial state conditions
  for(literalt l : netlist.initial)
    initial_BDDs.push_back(aig2bdd(l, BDDs));
    
  // transition conditions
  for(literalt l : netlist.transition)
    transition_relation.transition_conjuncts.push_back(aig2bdd(l, BDDs));

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
        CHECK_RETURN(netlist_property->second.has_value());
        DATA_INVARIANT(
          netlist_property->second.value().id() == ID_G,
          "assumed property must be G");
        auto &p = to_G_expr(netlist_property->second.value()).op();
        DATA_INVARIANT(
          p.id() == ID_literal, "assumed property must be G literal");
        auto l = to_literal_expr(p).get_literal();
        transition_relation.constraint_conjuncts.push_back(aig2bdd(l, BDDs));
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
