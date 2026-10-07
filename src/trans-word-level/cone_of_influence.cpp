/*******************************************************************\

Module: Cone of Influence Reduction

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "cone_of_influence.h"

#include <util/expr_util.h>
#include <util/graph.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include "next_symbol.h"

#include <unordered_map>
#include <unordered_set>

/*******************************************************************\

   Class: cone_of_influencet

 Purpose: Implementation of the cone-of-influence reduction

\*******************************************************************/

class cone_of_influencet
{
public:
  cone_of_influencet(const transt &_trans, const exprt::operandst &_seeds)
    : trans(_trans), seeds(_seeds)
  {
  }

  cone_of_influence_resultt operator()();

protected:
  const transt &trans;
  const exprt::operandst &seeds;

  typedef std::unordered_set<irep_idt> symbol_sett;

  enum class sectiont
  {
    INVAR,
    INIT,
    TRANS
  };

  /// The kind of a definition:
  /// INVAR: v == e, holds in every timeframe
  /// INIT: v == e, holds in timeframe 0
  /// NEXT: next(v) == e, defines v in timeframes 1, 2, ...
  enum class kindt
  {
    INVAR,
    INIT,
    NEXT
  };

  struct conjunctt
  {
    sectiont section;
    const exprt &expr;

    /// A definition is kept only if the variable is in the cone.
    /// A general constraint is always kept.
    bool definitional = false;
    irep_idt variable;
    kindt kind = kindt::INVAR;

    /// the current-state symbols and the next-state symbols
    /// that this conjunct depends on
    symbol_sett current_symbols, next_symbols;

    bool keep = false;

    conjunctt(sectiont _section, const exprt &_expr)
      : section(_section), expr(_expr)
    {
    }
  };

  std::vector<conjunctt> conjuncts;

  /// The definitions of a variable, as indices into \ref conjuncts
  struct definitionst
  {
    std::vector<std::size_t> invar, init, next;
  };

  std::unordered_map<irep_idt, definitionst> definitions;

  void collect_conjuncts(sectiont, const exprt &);
  void classify(conjunctt &);
  void find_definitions();
  void demote_conflicting_definitions();
  std::size_t demote_cyclic_definitions();
  void demote(const irep_idt &variable);
  void compute_closure();
  exprt conjunction_of_kept(sectiont) const;

  static void
  collect_symbols(const exprt &, symbol_sett &current, symbol_sett &next);

  static bool has_full_domain(const typet &);
};

/*******************************************************************\

Function: cone_of_influencet::collect_symbols

  Inputs: an expression

 Outputs: the identifiers of the symbols and next-state symbols
          in the expression

 Purpose:

\*******************************************************************/

void cone_of_influencet::collect_symbols(
  const exprt &expr,
  symbol_sett &current,
  symbol_sett &next)
{
  expr.visit_pre(
    [&current, &next](const exprt &node)
    {
      if(node.id() == ID_symbol)
        current.insert(to_symbol_expr(node).get_identifier());
      else if(node.id() == ID_next_symbol)
        next.insert(to_next_symbol_expr(node).identifier());
    });
}

/*******************************************************************\

Function: cone_of_influencet::collect_conjuncts

  Inputs:

 Outputs:

 Purpose: flatten a conjunction into \ref conjuncts

\*******************************************************************/

void cone_of_influencet::collect_conjuncts(sectiont section, const exprt &expr)
{
  if(expr.id() == ID_and)
  {
    for(auto &op : expr.operands())
      collect_conjuncts(section, op);
  }
  else if(expr.is_true())
  {
    // skip
  }
  else
  {
    conjuncts.emplace_back(section, expr);
    classify(conjuncts.back());
  }
}

/*******************************************************************\

Function: cone_of_influencet::has_full_domain

  Inputs: a type

 Outputs: true if every value of the solver's encoding of the type
          is a value of the type

 Purpose: A definition v == e can only be dropped if it can always
          be satisfied, which requires e to evaluate to a value in
          the domain of v. For types whose domain is the full set of
          bit patterns (bit-vectors, Booleans) this is trivially the
          case. For range or enumeration types, the backend may
          constrain v to its domain while e, e.g., a narrowing cast,
          may evaluate to a bit pattern outside it. We are
          conservative and consider only the former types.

\*******************************************************************/

bool cone_of_influencet::has_full_domain(const typet &type)
{
  if(
    type.id() == ID_bool || type.id() == ID_unsignedbv ||
    type.id() == ID_signedbv || type.id() == ID_bv ||
    type.id() == ID_verilog_unsignedbv || type.id() == ID_verilog_signedbv)
  {
    return true;
  }
  else if(type.id() == ID_array)
  {
    return has_full_domain(to_array_type(type).element_type());
  }
  else if(type.id() == ID_struct)
  {
    for(auto &component : to_struct_type(type).components())
      if(!has_full_domain(component.type()))
        return false;
    return true;
  }
  else
    return false;
}

/*******************************************************************\

Function: cone_of_influencet::classify

  Inputs:

 Outputs:

 Purpose: determine whether a conjunct is a candidate definition,
          and collect the symbols it depends on

\*******************************************************************/

void cone_of_influencet::classify(conjunctt &conjunct)
{
  const exprt &expr = conjunct.expr;

  if(expr.id() == ID_equal && has_full_domain(to_equal_expr(expr).lhs().type()))
  {
    auto &lhs = to_equal_expr(expr).lhs();
    auto &rhs = to_equal_expr(expr).rhs();

    if(lhs.id() == ID_symbol && conjunct.section == sectiont::INVAR)
    {
      conjunct.definitional = true;
      conjunct.variable = to_symbol_expr(lhs).get_identifier();
      conjunct.kind = kindt::INVAR;
    }
    else if(lhs.id() == ID_symbol && conjunct.section == sectiont::INIT)
    {
      conjunct.definitional = true;
      conjunct.variable = to_symbol_expr(lhs).get_identifier();
      conjunct.kind = kindt::INIT;
    }
    else if(lhs.id() == ID_symbol && conjunct.section == sectiont::TRANS)
    {
      // The SMV front-end places current-state assignments into
      // the transition constraint. These are instantiated in every
      // timeframe, and are thus invariant definitions, provided
      // that the rhs does not depend on the next state.
      conjunct.definitional = true;
      conjunct.variable = to_symbol_expr(lhs).get_identifier();
      conjunct.kind = kindt::INVAR;
    }
    else if(lhs.id() == ID_next_symbol && conjunct.section == sectiont::TRANS)
    {
      conjunct.definitional = true;
      conjunct.variable = to_next_symbol_expr(lhs).identifier();
      conjunct.kind = kindt::NEXT;
    }

    if(conjunct.definitional)
    {
      collect_symbols(rhs, conjunct.current_symbols, conjunct.next_symbols);

      // Definitions of the current state must not depend on the next state.
      if(conjunct.kind == kindt::NEXT || conjunct.next_symbols.empty())
        return;

      // Otherwise, this is a general constraint,
      // and the lhs is a dependency, too.
      conjunct.definitional = false;
      conjunct.current_symbols.insert(conjunct.variable);
      return;
    }
  }

  // general constraint
  conjunct.definitional = false;
  collect_symbols(expr, conjunct.current_symbols, conjunct.next_symbols);
}

/*******************************************************************\

Function: cone_of_influencet::find_definitions

  Inputs:

 Outputs:

 Purpose: populate the \ref definitions map

\*******************************************************************/

void cone_of_influencet::find_definitions()
{
  definitions.clear();

  for(std::size_t i = 0; i < conjuncts.size(); i++)
  {
    auto &conjunct = conjuncts[i];

    if(!conjunct.definitional)
      continue;

    auto &entry = definitions[conjunct.variable];

    switch(conjunct.kind)
    {
    case kindt::INVAR:
      entry.invar.push_back(i);
      break;
    case kindt::INIT:
      entry.init.push_back(i);
      break;
    case kindt::NEXT:
      entry.next.push_back(i);
      break;
    }
  }
}

/*******************************************************************\

Function: cone_of_influencet::demote

  Inputs:

 Outputs:

 Purpose: turn all definitions of the given variable into general
          constraints

\*******************************************************************/

void cone_of_influencet::demote(const irep_idt &variable)
{
  auto d_it = definitions.find(variable);
  if(d_it == definitions.end())
    return;

  for(auto list : {&d_it->second.invar, &d_it->second.init, &d_it->second.next})
  {
    for(auto index : *list)
    {
      auto &conjunct = conjuncts[index];
      conjunct.definitional = false;
      // The general constraint depends on the variable, too.
      if(conjunct.kind == kindt::NEXT)
        conjunct.next_symbols.insert(variable);
      else
        conjunct.current_symbols.insert(variable);
    }
  }

  definitions.erase(d_it);
}

/*******************************************************************\

Function: cone_of_influencet::demote_conflicting_definitions

  Inputs:

 Outputs:

 Purpose: Variables with multiple definitions of the same kind, or
          with an invariant definition in addition to an initial-state
          or next-state definition, are over-constrained. We cannot
          drop their definitions; they are treated as general
          constraints.

\*******************************************************************/

void cone_of_influencet::demote_conflicting_definitions()
{
  std::vector<irep_idt> to_demote;

  for(auto &entry : definitions)
  {
    auto &d = entry.second;

    bool conflict = d.invar.size() > 1 || d.init.size() > 1 ||
                    d.next.size() > 1 ||
                    (!d.invar.empty() && (!d.init.empty() || !d.next.empty()));

    if(conflict)
      to_demote.push_back(entry.first);
  }

  for(auto &variable : to_demote)
    demote(variable);
}

/*******************************************************************\

Function: cone_of_influencet::demote_cyclic_definitions

  Inputs:

 Outputs: the number of definitions demoted

 Purpose: Definitions that depend on each other within the same
          timeframe (e.g., a == !b and b == a) may be unsatisfiable,
          and hence cannot be dropped. We find the cycles and treat
          the definitions on them as general constraints.

          We distinguish timeframe 0 from the later timeframes, since
          the initial-state definitions only apply to timeframe 0,
          and the next-state definitions only to later timeframes.

\*******************************************************************/

std::size_t cone_of_influencet::demote_cyclic_definitions()
{
  // one node per variable with a definition
  std::vector<irep_idt> variables;
  std::unordered_map<irep_idt, grapht<>::node_indext> node_map;

  for(auto &entry : definitions)
  {
    node_map[entry.first] = variables.size();
    variables.push_back(entry.first);
  }

  // timeframe 0: INIT and INVAR definitions
  grapht<> graph_0;
  // timeframe >0: NEXT and INVAR definitions
  grapht<> graph_1;

  graph_0.resize(variables.size());
  graph_1.resize(variables.size());

  auto add_edges = [this, &node_map](
                     grapht<> &graph,
                     grapht<>::node_indext from,
                     const std::vector<std::size_t> &conjunct_indices,
                     bool next)
  {
    for(auto index : conjunct_indices)
    {
      auto &conjunct = conjuncts[index];
      auto &symbols = next ? conjunct.next_symbols : conjunct.current_symbols;
      for(auto &symbol : symbols)
      {
        auto to_it = node_map.find(symbol);
        if(to_it != node_map.end())
          graph.add_edge(from, to_it->second);
      }
    }
  };

  for(auto &entry : definitions)
  {
    auto from = node_map[entry.first];
    auto &d = entry.second;
    add_edges(graph_0, from, d.init, false);
    add_edges(graph_0, from, d.invar, false);
    add_edges(graph_1, from, d.next, true);
    add_edges(graph_1, from, d.invar, false);
  }

  // Find the variables that are on a cycle.
  std::unordered_set<irep_idt> cyclic;

  for(auto graph : {&graph_0, &graph_1})
  {
    if(graph->empty())
      continue;

    std::vector<grapht<>::node_indext> scc_nr;
    auto no_sccs = graph->SCCs(scc_nr);

    std::vector<std::size_t> scc_size(no_sccs, 0);
    for(auto nr : scc_nr)
      scc_size[nr]++;

    for(grapht<>::node_indext n = 0; n < variables.size(); n++)
    {
      // nontrivial SCC, or self-loop
      if(scc_size[scc_nr[n]] > 1 || graph->has_edge(n, n))
        cyclic.insert(variables[n]);
    }
  }

  std::size_t count = 0;

  for(auto &variable : cyclic)
  {
    auto &d = definitions[variable];
    count += d.invar.size() + d.init.size() + d.next.size();
    demote(variable);
  }

  return count;
}

/*******************************************************************\

Function: cone_of_influencet::compute_closure

  Inputs:

 Outputs:

 Purpose: mark the conjuncts to be kept

\*******************************************************************/

void cone_of_influencet::compute_closure()
{
  symbol_sett in_cone;
  std::vector<irep_idt> worklist;

  auto add = [&in_cone, &worklist](const symbol_sett &symbols)
  {
    for(auto &symbol : symbols)
      if(in_cone.insert(symbol).second)
        worklist.push_back(symbol);
  };

  // The seeds
  for(auto &seed : seeds)
  {
    symbol_sett current, next;
    collect_symbols(seed, current, next);
    add(current);
    add(next);
  }

  // The general constraints are always kept,
  // and the symbols they depend on are in the cone.
  for(auto &conjunct : conjuncts)
  {
    if(!conjunct.definitional)
    {
      conjunct.keep = true;
      add(conjunct.current_symbols);
      add(conjunct.next_symbols);
    }
  }

  // Now compute the backwards closure over the definitions.
  while(!worklist.empty())
  {
    auto variable = worklist.back();
    worklist.pop_back();

    auto d_it = definitions.find(variable);
    if(d_it == definitions.end())
      continue; // no definition, e.g., an input

    for(auto list :
        {&d_it->second.invar, &d_it->second.init, &d_it->second.next})
    {
      for(auto index : *list)
      {
        auto &conjunct = conjuncts[index];
        conjunct.keep = true;
        add(conjunct.current_symbols);
        add(conjunct.next_symbols);
      }
    }
  }
}

/*******************************************************************\

Function: cone_of_influencet::conjunction_of_kept

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt cone_of_influencet::conjunction_of_kept(sectiont section) const
{
  exprt::operandst result;

  for(auto &conjunct : conjuncts)
    if(conjunct.section == section && conjunct.keep)
      result.push_back(conjunct.expr);

  return conjunction(result);
}

/*******************************************************************\

Function: cone_of_influencet::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cone_of_influence_resultt cone_of_influencet::operator()()
{
  conjuncts.clear();
  collect_conjuncts(sectiont::INVAR, trans.invar());
  collect_conjuncts(sectiont::INIT, trans.init());
  collect_conjuncts(sectiont::TRANS, trans.trans());

  find_definitions();
  demote_conflicting_definitions();
  auto cyclic_definitions = demote_cyclic_definitions();
  compute_closure();

  cone_of_influence_resultt result{
    transt{
      ID_trans,
      conjunction_of_kept(sectiont::INVAR),
      conjunction_of_kept(sectiont::INIT),
      conjunction_of_kept(sectiont::TRANS),
      trans.type()},
    {}};

  auto &statistics = result.statistics;
  statistics.cyclic_definitions = cyclic_definitions;

  symbol_sett state_variables, state_variables_kept;

  for(auto &conjunct : conjuncts)
  {
    switch(conjunct.section)
    {
    case sectiont::INVAR:
      statistics.invar_constraints++;
      if(conjunct.keep)
        statistics.invar_constraints_kept++;
      break;

    case sectiont::INIT:
      statistics.init_constraints++;
      if(conjunct.keep)
        statistics.init_constraints_kept++;
      break;

    case sectiont::TRANS:
      statistics.trans_constraints++;
      if(conjunct.keep)
        statistics.trans_constraints_kept++;
      break;
    }

    // Count the variables that have a next-state definition
    if(conjunct.expr.id() == ID_equal)
    {
      auto &lhs = to_equal_expr(conjunct.expr).lhs();
      if(lhs.id() == ID_next_symbol)
      {
        auto &identifier = to_next_symbol_expr(lhs).identifier();
        state_variables.insert(identifier);
        if(conjunct.keep)
          state_variables_kept.insert(identifier);
      }
    }
  }

  statistics.state_variables = state_variables.size();
  statistics.state_variables_kept = state_variables_kept.size();

  return result;
}

/*******************************************************************\

Function: cone_of_influence

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cone_of_influence_resultt
cone_of_influence(const transt &trans, const exprt::operandst &seeds)
{
  return cone_of_influencet{trans, seeds}();
}

/*******************************************************************\

Function: cone_of_influence_resultt::report

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cone_of_influence_resultt::report(messaget &message) const
{
  auto &s = statistics;

  message.statistics() << "Cone of influence: " << s.state_variables_kept
                       << " of " << s.state_variables << " state variables, "
                       << s.constraints_kept() << " of " << s.constraints()
                       << " constraints"
                       << " (invar " << s.invar_constraints_kept << '/'
                       << s.invar_constraints << ", init "
                       << s.init_constraints_kept << '/' << s.init_constraints
                       << ", trans " << s.trans_constraints_kept << '/'
                       << s.trans_constraints << ')' << messaget::eom;

  if(s.cyclic_definitions != 0)
  {
    message.statistics() << "Cone of influence: " << s.cyclic_definitions
                         << " definitions are cyclic and were kept"
                         << messaget::eom;
  }
}
