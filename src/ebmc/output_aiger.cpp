/*******************************************************************\

Module: Output AIGER

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "output_aiger.h"

#include <solvers/prop/literal_expr.h>
#include <trans-netlist/netlist.h>

#include <map>
#include <ostream>
#include <string>
#include <unordered_set>
#include <vector>

extern "C"
{
#include <aiger-1.9/aiger.h>
}

/// Convert a literalt to an AIGER literal.
/// AIGER uses variable 0 for the constant FALSE.
/// CBMC variables start at 0, so we map var_no v to AIGER variable v+1.
static unsigned to_aiger_lit(literalt l)
{
  if(l.is_false())
    return aiger_false;
  if(l.is_true())
    return aiger_true;
  return ((l.var_no() + 1) << 1) | (l.sign() ? 1u : 0u);
}

/// Sanitize a string for use as an AIGER symbol name. The AIGER
/// symbol-table format is "<type><pos> <name>\n" where the name
/// extends to the end of the line: the reader (aiger.c) consumes
/// characters up to '\n', and the writer asserts the name is
/// non-empty. Spaces are therefore fine (and can occur, e.g., in
/// VHDL extended identifiers), but an embedded newline would
/// corrupt the symbol table, a carriage return would pollute
/// round-trips, and an empty name would trip the writer's
/// assertion. Replace control characters by '_' and map an empty
/// name to "_".
static std::string aiger_symbol_name(const std::string &src)
{
  std::string result = src;
  for(auto &ch : result)
    if(static_cast<unsigned char>(ch) < ' ')
      ch = '_';
  if(result.empty())
    result = "_";
  return result;
}

/// Get the body literal for an invariant property (G/AG/sva_always).
/// Returns {} if the property is not a supported invariant form.
static std::optional<literalt>
invariant_literal(const std::optional<exprt> &netlist_expr)
{
  if(!netlist_expr.has_value())
    return {};

  auto &expr = netlist_expr.value();

  // Must be G(...), AG(...), or sva_always(...)
  if(expr.id() != ID_G && expr.id() != ID_AG && expr.id() != ID_sva_always)
  {
    return {};
  }

  auto &body = to_unary_expr(expr).op();

  if(body.id() != ID_literal)
    return {};

  return to_literal_expr(body).get_literal();
}

/// Split a netlist literal into the conjuncts given by its
/// (non-negated) AND nodes. The constant TRUE yields no conjunct.
/// This uses an explicit stack, as the conjunction may be deep, and
/// visits shared AND nodes once.
static bvt flatten_conjunction(const netlistt &netlist, const bvt &literals)
{
  bvt conjuncts;
  std::vector<literalt> stack(literals.rbegin(), literals.rend());
  std::unordered_set<literalt::var_not> visited;

  while(!stack.empty())
  {
    literalt l = stack.back();
    stack.pop_back();

    if(l.is_true())
      continue;

    if(!l.is_constant() && !l.sign() && netlist.nodes[l.var_no()].is_and())
    {
      if(!visited.insert(l.var_no()).second)
        continue; // already flattened
      const auto &node = netlist.nodes[l.var_no()];
      stack.push_back(node.b);
      stack.push_back(node.a);
    }
    else
      conjuncts.push_back(l);
  }

  return conjuncts;
}

void output_aiger(const netlistt &netlist, std::ostream &out)
{
  aiger *aig = aiger_init();

  // Add inputs
  for(auto var_no : netlist.var_map.inputs)
  {
    unsigned lit = to_aiger_lit(literalt{var_no, false});
    // Name the input from the reverse map (e.g. "a[3]"), so
    // downstream gate-level tools can check operand ordering.
    auto it = netlist.var_map.reverse_map.find(var_no);
    if(it != netlist.var_map.reverse_map.end())
    {
      std::string name = aiger_symbol_name(
        id2string(it->second.id) + '[' + std::to_string(it->second.bit_nr) +
        ']');
      aiger_add_input(aig, lit, name.c_str());
    }
    else
      aiger_add_input(aig, lit, nullptr);
  }

  // Non-deterministic variables, e.g., wires without a driver, are
  // AIGER inputs as well. They differ from inputs in that they are
  // chosen in every state, which is what AIGER inputs are.
  for(auto var_no : netlist.var_map.nondets)
    aiger_add_input(aig, to_aiger_lit(literalt{var_no, false}), nullptr);

  // The initial-state constraint is a conjunction. Conjuncts that fix
  // the value of a latch become its AIGER reset value. Any other
  // conjuncts are 'residual' and are encoded below.
  std::map<unsigned, bool> reset_values;
  bvt residual_initial;

  {
    bvt conjuncts = flatten_conjunction(netlist, netlist.initial);

    for(auto l : conjuncts)
    {
      if(!l.is_constant() && netlist.var_map.latches.count(l.var_no()) != 0)
      {
        bool value = !l.sign();
        auto result = reset_values.emplace(l.var_no(), value);
        if(result.second || result.first->second == value)
          continue; // reset value recorded or already given
      }

      residual_initial.push_back(l);
    }
  }

  // Add latches
  for(auto var_no : netlist.var_map.latches)
  {
    unsigned lit = to_aiger_lit(literalt{var_no, false});
    // Find the 'next' literal for this latch from the var_map
    auto it = netlist.var_map.reverse_map.find(var_no);
    PRECONDITION(it != netlist.var_map.reverse_map.end());
    literalt next = netlist.var_map.get_next(it->second);
    unsigned next_lit = to_aiger_lit(next);
    aiger_add_latch(aig, lit, next_lit, nullptr);

    // Latches without reset value are uninitialised, which AIGER 1.9
    // denotes by using the latch literal as reset value.
    auto reset_it = reset_values.find(var_no);
    if(reset_it == reset_values.end())
      aiger_add_reset(aig, lit, lit);
    else
      aiger_add_reset(aig, lit, reset_it->second ? 1 : 0);
  }

  // Residual initial-state constraints use an additional latch
  // 'first', which is 1 in the initial state only, and an AIGER
  // constraint !first || c, i.e., !(first && !c), for each residual
  // constraint c.
  unsigned next_aiger_var = netlist.number_of_nodes() + 1;

  if(!residual_initial.empty())
  {
    unsigned first_lit = aiger_var2lit(next_aiger_var++);
    aiger_add_latch(aig, first_lit, aiger_false, nullptr);
    aiger_add_reset(aig, first_lit, 1);

    for(auto l : residual_initial)
    {
      unsigned and_lit = aiger_var2lit(next_aiger_var++);
      aiger_add_and(aig, and_lit, first_lit, aiger_not(to_aiger_lit(l)));
      aiger_add_constraint(aig, aiger_not(and_lit), nullptr);
    }
  }

  // Add AND gates
  for(literalt::var_not i = 0; i < netlist.number_of_nodes(); i++)
  {
    const auto &node = netlist.nodes[i];
    if(node.is_and())
    {
      unsigned lhs = to_aiger_lit(literalt{i, false});
      unsigned rhs0 = to_aiger_lit(node.a);
      unsigned rhs1 = to_aiger_lit(node.b);
      aiger_add_and(aig, lhs, rhs0, rhs1);
    }
  }

  // Add constraints
  for(auto l : netlist.transition)
  {
    unsigned lit = to_aiger_lit(l);
    aiger_add_constraint(aig, lit, nullptr);
  }

  // Add module outputs. These are circuit outputs in the AIGER
  // sense (e.g. the product bits of a multiplier), as consumed by
  // gate-level tools such as AMulet. Emitted per bit, LSB first,
  // named "id[bit]". Note the bit's current literal may be negated;
  // to_aiger_lit preserves the sign.
  for(const auto &map_it : netlist.var_map.sorted())
  {
    const auto &id = map_it->first;
    const auto &var = map_it->second;
    if(!var.is_output())
      continue;
    for(std::size_t bit_nr = 0; bit_nr < var.bits.size(); bit_nr++)
    {
      unsigned lit = to_aiger_lit(var.bits[bit_nr].current);
      std::string name =
        aiger_symbol_name(id2string(id) + '[' + std::to_string(bit_nr) + ']');
      aiger_add_output(aig, lit, name.c_str());
    }
  }

  // Add properties as bad state outputs.
  // A bad state is a state that violates the property,
  // i.e., the negation of the property body literal.
  for(auto &[id, netlist_expr] : netlist.properties)
  {
    auto l = invariant_literal(netlist_expr);
    if(l.has_value())
    {
      unsigned bad_lit = to_aiger_lit(!l.value());
      aiger_add_bad(aig, bad_lit, aiger_symbol_name(id2string(id)).c_str());
    }
  }

  // Write in ASCII mode to the stream
  auto put_fn = [](char ch, void *s) -> int
  {
    auto *os = static_cast<std::ostream *>(s);
    os->put(ch);
    return os->good() ? static_cast<unsigned char>(ch) : EOF;
  };

  aiger_write_generic(aig, aiger_ascii_mode, &out, put_fn);

  aiger_reset(aig);
}
