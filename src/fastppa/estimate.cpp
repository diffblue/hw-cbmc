/*******************************************************************\

Module: FastPPA whole-design graph estimator

Author: Kiro

\*******************************************************************/

/// \file
/// Whole-design graph estimator.
///
/// The design is turned into one graph whose nodes are hash-consed: two
/// occurrences of the same operator applied to the same operands are the
/// same node, whether they occur in the same next-state function, in
/// different ones, or behind a named wire. Wires are inlined. Each node is
/// costed once. Only logic that reaches a top-level output port, directly or
/// through registers, is costed. Timing is the longest path through the
/// graph, starting at inputs (0 ps) and registers (clock-to-Q), and ending
/// at outputs and register inputs.
///
/// The only rules applied are ones that hold for any synthesis tool:
/// - constant propagation (simplify_expr, also through wires and through
///   registers whose next state is a constant or the register itself);
/// - operators with a constant shift distance, bit or array index are wiring;
/// - bitwise operators with a constant operand only need gates for the bits
///   the constant does not decide;
/// - single-fanout chains of the same associative operator are one n-ary
///   operator, implemented as a tree that is balanced by arrival time.
/// The cost of each operator is a function of its width (and array size),
/// fitted on single-operator designs only (see fit.py).

#include "estimate.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <ebmc/ebmc_error.h>
#include <solvers/flattening/boolbv_width.h>

#include "cost_table.h"

#include <algorithm>
#include <cmath>
#include <functional>
#include <optional>
#include <queue>
#include <unordered_map>
#include <unordered_set>

namespace
{
// Leaf kinds of the graph, besides ID_constant.
const irep_idt ID_fastppa_input = "fastppa_input";
const irep_idt ID_fastppa_register = "fastppa_register";
// A value that is constant but not known: an undriven wire, or a register
// that is never updated.
const irep_idt ID_fastppa_opaque = "fastppa_opaque";
// A wire that is assembled from separately assigned parts: wiring.
const irep_idt ID_fastppa_assemble = "fastppa_assemble";
// Placeholder symbols that stand for graph nodes during simplification.
const std::string placeholder_prefix = "fastppa::node::";

struct gnodet
{
  irep_idt id;
  typet type;
  std::vector<std::size_t> ops;
  exprt value; // constants: the constant; leaves: the symbol
  source_locationt source_location = {};
};

struct keyt
{
  irept shell; // the expression with its graph operands removed
  std::vector<std::size_t> ops;

  bool operator==(const keyt &other) const
  {
    return ops == other.ops && shell == other.shell;
  }
};

struct key_hasht
{
  std::size_t operator()(const keyt &key) const
  {
    std::size_t h = key.shell.hash();
    for(auto op : key.ops)
      h = h * 1000003u ^ std::hash<std::size_t>{}(op);
    return h;
  }
};

bool is_commutative(const irep_idt &id)
{
  return id == ID_plus || id == ID_mult || id == ID_bitand || id == ID_bitor ||
         id == ID_bitxor || id == ID_and || id == ID_or || id == ID_xor ||
         id == ID_equal || id == ID_notequal || id == ID_bitnand ||
         id == ID_bitnor || id == ID_bitxnor;
}

bool is_associative(const irep_idt &id)
{
  return id == ID_plus || id == ID_mult || id == ID_bitand || id == ID_bitor ||
         id == ID_bitxor || id == ID_and || id == ID_or || id == ID_xor;
}

bool is_unsupported_type(const typet &type)
{
  return type.id() == ID_floatbv || type.id() == ID_fixedbv ||
         type.id() == ID_real || type.id() == ID_verilog_real ||
         type.id() == ID_verilog_shortreal ||
         type.id() == ID_verilog_realtime || type.id() == ID_string;
}

/// The graph of one design, for a given set of registers that are known to
/// be constant.
class grapht
{
public:
  grapht(
    const transt &_trans,
    const std::vector<symbol_exprt> &_state_vars,
    const std::vector<symbol_exprt> &_outputs,
    const namespacet &_ns,
    const std::unordered_map<irep_idt, exprt> &_constant_registers,
    message_handlert &_message_handler)
    : trans(_trans),
      state_vars(_state_vars),
      output_symbols(_outputs),
      ns(_ns),
      constant_registers(_constant_registers),
      message(_message_handler)
  {
    collect_definitions();
  }

  std::vector<gnodet> nodes;

  /// register name -> node of its next-state function
  std::unordered_map<irep_idt, std::size_t> next_state;

  /// register name -> its leaf node
  std::unordered_map<irep_idt, std::size_t> register_node;

  /// top-level output port nodes, and their names
  std::vector<std::size_t> outputs;
  std::vector<irep_idt> output_names;

  std::size_t undriven_symbols = 0;

  void build()
  {
    for(auto &[name, rhs] : next_state_definitions)
      if(constant_registers.find(name) == constant_registers.end())
        next_state[name] = build_rec(rhs);

    for(auto &output : output_symbols)
    {
      outputs.push_back(build_rec(output));
      output_names.push_back(output.get_identifier());
    }
  }

  bool is_constant(std::size_t n) const
  {
    return nodes[n].id == ID_constant;
  }

protected:
  const transt &trans;
  const std::vector<symbol_exprt> &state_vars;
  const std::vector<symbol_exprt> &output_symbols;
  const namespacet &ns;
  const std::unordered_map<irep_idt, exprt> &constant_registers;
  messaget message;

  std::unordered_map<irep_idt, exprt> wire_definitions;
  std::unordered_map<irep_idt, std::vector<exprt>> partial_definitions;
  std::map<irep_idt, exprt> next_state_definitions; // ordered: deterministic
  std::unordered_set<irep_idt> state_variables;
  std::unordered_map<irep_idt, std::size_t> symbol_node;
  std::unordered_set<irep_idt> in_progress;
  std::unordered_map<keyt, std::size_t, key_hasht> node_map;
  std::size_t simplify_depth = 0;

  static void conjuncts(const exprt &expr, std::vector<exprt> &dest)
  {
    if(expr.id() == ID_and)
      for(auto &op : expr.operands())
        conjuncts(op, dest);
    else if(!expr.is_true())
      dest.push_back(expr);
  }

  void collect_definitions()
  {
    for(auto &v : state_vars)
      state_variables.insert(v.get_identifier());

    std::vector<exprt> invar;
    conjuncts(trans.invar(), invar);
    for(auto &c : invar)
    {
      if(c.id() == ID_equal && to_equal_expr(c).lhs().id() == ID_symbol)
      {
        auto &eq = to_equal_expr(c);
        auto id = to_symbol_expr(eq.lhs()).get_identifier();
        if(!wire_definitions.emplace(id, eq.rhs()).second)
          message.warning()
            << "wire " << id << " has several definitions" << messaget::eom;
      }
      else if(c.id() == ID_equal)
      {
        // an assignment to a part of a wire: find the wire
        const exprt *lhs = &to_equal_expr(c).lhs();
        while(lhs->id() != ID_symbol && lhs->operands().size() >= 1 &&
              (lhs->id() == ID_index || lhs->id() == ID_extractbits ||
               lhs->id() == ID_extractbit || lhs->id() == ID_member ||
               lhs->id() == ID_shl || lhs->id() == ID_lshr ||
               lhs->id() == ID_typecast))
        {
          lhs = &to_multi_ary_expr(*lhs).op0();
        }
        if(lhs->id() != ID_symbol)
          throw ebmc_errort{} << "unsupported state constraint with left-hand "
                              << "side " << to_equal_expr(c).lhs().id();
        partial_definitions[to_symbol_expr(*lhs).get_identifier()].push_back(
          to_equal_expr(c).rhs());
      }
      else
        throw ebmc_errort{} << "unsupported state constraint: " << c.id();
    }

    std::vector<exprt> next;
    conjuncts(trans.trans(), next);
    for(auto &c : next)
    {
      if(c.id() == ID_equal && to_equal_expr(c).lhs().id() == ID_next_symbol)
      {
        auto &eq = to_equal_expr(c);
        auto id = eq.lhs().get(ID_identifier);
        if(!next_state_definitions.emplace(id, eq.rhs()).second)
          throw ebmc_errort{} << "register " << id
                              << " has several next-state functions";
      }
      else
        throw ebmc_errort{} << "unsupported transition constraint: " << c.id();
    }
  }

  std::size_t add_node(gnodet node, const keyt &key)
  {
    auto it = node_map.find(key);
    if(it != node_map.end())
      return it->second;
    nodes.push_back(std::move(node));
    node_map.emplace(key, nodes.size() - 1);
    return nodes.size() - 1;
  }

  std::size_t leaf(const irep_idt &kind, const exprt &value)
  {
    gnodet node{kind, value.type(), {}, value};
    exprt shell{kind, value.type()};
    shell.add(ID_value) = value;
    return add_node(std::move(node), keyt{shell, {}});
  }

  std::size_t symbol_rec(const symbol_exprt &symbol_expr)
  {
    const auto id = symbol_expr.get_identifier();

    if(id.starts_with(placeholder_prefix))
      return std::stoul(id2string(id).substr(placeholder_prefix.size()));

    auto it = symbol_node.find(id);
    if(it != symbol_node.end())
      return it->second;

    if(is_unsupported_type(symbol_expr.type()))
      throw ebmc_errort{} << "unsupported type " << symbol_expr.type().id()
                          << " of " << id;

    std::size_t result;

    if(state_variables.count(id) != 0)
    {
      auto c_it = constant_registers.find(id);
      if(c_it == constant_registers.end())
      {
        result = leaf(ID_fastppa_register, symbol_expr);
        register_node[id] = result;
      }
      else if(c_it->second.is_constant())
        result = leaf(ID_constant, c_it->second);
      else
        result = leaf(ID_fastppa_opaque, symbol_expr);
    }
    else if(auto w_it = wire_definitions.find(id);
            w_it != wire_definitions.end())
    {
      if(!in_progress.insert(id).second)
        throw ebmc_errort{} << "combinational loop through " << id;
      result = build_rec(w_it->second);
      in_progress.erase(id);
    }
    else if(auto p_it = partial_definitions.find(id);
            p_it != partial_definitions.end())
    {
      // Parts may legitimately read other parts of the same wire; such a
      // read is treated as an opaque value rather than as a loop.
      if(!in_progress.insert(id).second)
        return leaf(ID_fastppa_opaque, symbol_expr);
      std::vector<std::size_t> parts;
      for(auto &rhs : p_it->second)
        parts.push_back(build_rec(rhs));
      in_progress.erase(id);
      exprt shell{ID_fastppa_assemble, symbol_expr.type()};
      result = add_node(
        gnodet{ID_fastppa_assemble, symbol_expr.type(), parts, nil_exprt{}},
        keyt{shell, parts});
    }
    else
    {
      const symbolt *symbol;
      bool input = !ns.lookup(id, symbol) && symbol->is_input;
      if(input)
        result = leaf(ID_fastppa_input, symbol_expr);
      else
      {
        ++undriven_symbols;
        message.debug() << "undriven: " << id << messaget::eom;
        result = leaf(ID_fastppa_opaque, symbol_expr);
      }
    }

    symbol_node[id] = result;
    return result;
  }

  exprt placeholder(std::size_t n) const
  {
    if(is_constant(n))
      return nodes[n].value;
    return symbol_exprt{placeholder_prefix + std::to_string(n), nodes[n].type};
  }

  // Which operands of expr are values (graph nodes)? Designators are not.
  static bool is_value_operand(const exprt &expr, std::size_t i)
  {
    if(expr.id() == ID_with && expr.operands()[0].type().id() != ID_array)
      return i % 2 == 0; // struct/union with: odd operands are designators
    if(expr.id() == ID_member)
      return i == 0;
    return true;
  }

  // A constant select from a wire whose definition is an array or a
  // concatenation resolves to the selected part of the definition, so that
  // parts of a wire can depend on other parts of the same wire.
  std::optional<std::size_t> select_from_definition(const exprt &expr)
  {
    if(
      expr.id() != ID_index && expr.id() != ID_extractbit &&
      expr.id() != ID_extractbits)
      return {};
    const auto &src = to_binary_expr(expr).op0();
    if(src.id() != ID_symbol)
      return {};
    const auto id = to_symbol_expr(src).get_identifier();
    if(state_variables.count(id) != 0)
      return {};
    auto def_it = wire_definitions.find(id);
    if(def_it == wire_definitions.end())
      return {};
    const exprt &def = def_it->second;
    // the index may be a constant expression, e.g. i - 1 after unrolling
    auto k_opt =
      numeric_cast<mp_integer>(simplify_expr(to_binary_expr(expr).op1(), ns));
    if(!k_opt.has_value() || *k_opt < 0)
      return {};
    const auto k = numeric_cast_v<std::size_t>(*k_opt);

    std::optional<exprt> part;

    if(expr.id() == ID_index && def.id() == ID_array)
    {
      if(k < def.operands().size())
        part = def.operands()[k];
    }
    else if(expr.id() != ID_index && def.id() == ID_concatenation)
    {
      // operands are most significant first
      const std::size_t sel_width =
        expr.id() == ID_extractbit ? 1 : width_of(expr.type());
      std::size_t offset = 0;
      for(auto it = def.operands().rbegin(); it != def.operands().rend(); ++it)
      {
        const std::size_t w = width_of(it->type());
        if(k >= offset && k + sel_width <= offset + w)
        {
          if(w == sel_width && it->type() == expr.type())
            part = *it;
          else if(expr.id() == ID_extractbit)
            part = extractbit_exprt{*it, k - offset};
          else
            part = extractbits_exprt{*it, k - offset, expr.type()};
          break;
        }
        offset += w;
      }
    }

    if(!part.has_value())
      return {};

    const irep_idt key = id2string(id) + "[" + std::to_string(k) + "]";
    if(!in_progress.insert(key).second)
      throw ebmc_errort{} << "combinational loop through " << key;
    auto result = build_rec(*part);
    in_progress.erase(key);
    return result;
  }

  std::size_t width_of(const typet &type) const
  {
    auto w = boolbv_widtht{ns}.get_width_opt(type);
    if(!w.has_value())
      throw ebmc_errort{} << "cannot determine the width of type " << type.id();
    return *w;
  }

  std::size_t build_rec(const exprt &expr)
  {
    if(auto selected = select_from_definition(expr))
      return *selected;

    if(is_unsupported_type(expr.type()))
      throw ebmc_errort{} << "unsupported type " << expr.type().id();

    if(expr.id() == ID_symbol)
      return symbol_rec(to_symbol_expr(expr));
    else if(expr.is_constant())
      return leaf(ID_constant, expr);
    else if(expr.id() == ID_nondet_symbol)
      return leaf(ID_fastppa_input, expr);
    else if(expr.id() == ID_next_symbol)
      throw ebmc_errort{} << "unexpected next-state reference";

    // Only the taken branch of an if with a constant condition is
    // hardware; the other one may refer to elements that do not exist,
    // e.g., the guard i >= 1 around acc[i - 1] for i = 0.
    if(expr.id() == ID_if)
    {
      const auto &if_expr = to_if_expr(expr);
      const auto c = build_rec(if_expr.cond());
      if(is_constant(c))
        return build_rec(
          nodes[c].value.is_true() ? if_expr.true_case()
                                   : if_expr.false_case());
    }

    std::vector<std::size_t> ops;
    std::vector<std::size_t> op_index;
    exprt shell = expr;
    bool any_constant = false, any_non_constant = false;
    for(std::size_t i = 0; i < expr.operands().size(); ++i)
    {
      if(!is_value_operand(expr, i))
        continue;
      auto n = build_rec(expr.operands()[i]);
      ops.push_back(n);
      op_index.push_back(i);
      shell.operands()[i] = nil_exprt{};
      (is_constant(n) ? any_constant : any_non_constant) = true;
    }

    // Constant propagation through wires and registers: simplify with the
    // operands replaced by constants or placeholders.
    if(any_constant && simplify_depth < 4)
    {
      exprt e = expr;
      for(std::size_t j = 0; j < ops.size(); ++j)
        e.operands()[op_index[j]] = placeholder(ops[j]);
      exprt s = simplify_expr(e, ns);
      if(s.is_constant())
        return leaf(ID_constant, s);
      if(s != e)
      {
        ++simplify_depth;
        auto result = build_rec(s);
        --simplify_depth;
        return result;
      }
    }

    (void)any_non_constant;

    if(is_commutative(expr.id()) && op_index.size() == expr.operands().size())
      std::sort(ops.begin(), ops.end());

    keyt key{shell, ops};
    gnodet node{expr.id(), expr.type(), ops, nil_exprt{}};
    node.source_location = expr.source_location();
    if(expr.id() == ID_with || expr.id() == ID_member)
      node.value = shell; // keeps designators
    return add_node(std::move(node), key);
  }
};

/// Costs a graph.
class costert
{
public:
  costert(
    const grapht &_graph,
    const cost_tablet &_table,
    const namespacet &_ns)
    : graph(_graph), table(_table), boolbv_width(_ns)
  {
  }

  estimation_resultt run()
  {
    mark_live();
    count_fanout();

    arrival.assign(graph.nodes.size(), 0);
    depth.assign(graph.nodes.size(), 0);
    const double clock_to_q = table("register").delay(1, 0);

    for(std::size_t n = 0; n < graph.nodes.size(); ++n)
    {
      if(!live[n] || absorbed(n))
        continue;
      const auto &node = graph.nodes[n];
      if(node.id == ID_fastppa_register)
        arrival[n] = clock_to_q;
      else if(
        node.id == ID_constant || node.id == ID_fastppa_input ||
        node.id == ID_fastppa_opaque)
        arrival[n] = 0;
      else
        cost_node(n);
    }

    // registers
    for(auto &[name, reg] : graph.register_node)
    {
      if(!live[reg])
        continue;
      auto w = width(graph.nodes[reg].type);
      result.register_bits += w;
      const auto &r = table("register");
      result.register_area_um2 += r.area(w);
      result.data_energy_fj += r.energy(w);
      result.leakage_uw += r.leakage(w);
      result.clock_energy_fj += table("clock").energy(w);
    }

    // endpoints
    std::vector<std::pair<double, critical_patht>> paths;
    auto endpoint =
      [this, &paths](std::size_t n, const irep_idt &name, bool is_register)
    {
      result.critical_path_ps = std::max(result.critical_path_ps, arrival[n]);
      result.combinational_depth =
        std::max(result.combinational_depth, depth[n]);
      paths.emplace_back(
        arrival[n], critical_patht{name, is_register, arrival[n], {}});
      trace(n, paths.back().second.steps);
    };
    for(std::size_t i = 0; i < graph.outputs.size(); ++i)
    {
      // an output that is a register is reported as that register
      if(graph.nodes[graph.outputs[i]].id == ID_fastppa_register)
        continue;
      endpoint(graph.outputs[i], graph.output_names[i], false);
    }
    for(auto &[name, n] : graph.next_state)
    {
      auto r_it = graph.register_node.find(name);
      if(r_it != graph.register_node.end() && live[r_it->second])
        endpoint(n, name, true);
    }
    std::stable_sort(
      paths.begin(),
      paths.end(),
      [](const auto &a, const auto &b) { return a.first > b.first; });
    for(auto &path : paths)
      if(path.first > 0)
        result.critical_paths.push_back(std::move(path.second));

    result.total_area_um2 =
      result.register_area_um2 + result.combinational_area_um2;
    return result;
  }

  /// area per cost-table kind, for diagnostics
  std::map<std::string, std::pair<std::size_t, double>> area_by_kind;

protected:
  const grapht &graph;
  const cost_tablet &table;
  boolbv_widtht boolbv_width;

  std::vector<bool> live;
  std::vector<std::size_t> fanout;
  std::vector<double> arrival;
  std::vector<std::size_t> depth;
  estimation_resultt result;

  std::size_t width(const typet &type) const
  {
    auto w = boolbv_width.get_width_opt(type);
    if(!w.has_value() || *w == 0)
      throw ebmc_errort{} << "cannot determine the width of type " << type.id();
    return *w;
  }

  /// The operands of n as costed: the leaves of a balanced chain, the
  /// operands of an absorbed shift.
  std::vector<std::size_t> inputs_of(std::size_t n) const
  {
    const auto &node = graph.nodes[n];
    if(is_associative(node.id))
    {
      std::vector<std::size_t> result;
      leaves(n, result);
      return result;
    }
    if(aligned_select(n).has_value())
      return graph.nodes[node.ops[0]].ops;
    return node.ops;
  }

  /// The steps of the latest-arriving path to n, from its start.
  void trace(std::size_t n, std::vector<critical_patht::stept> &steps) const
  {
    std::vector<critical_patht::stept> reversed;
    for(std::size_t guard = 0; guard < graph.nodes.size(); ++guard)
    {
      const auto &node = graph.nodes[n];
      const auto ops = inputs_of(n);
      double latest = 0;
      std::optional<std::size_t> pred;
      for(auto op : ops)
        if(!pred.has_value() || arrival[op] > latest)
        {
          latest = arrival[op];
          pred = op;
        }
      // only steps that add delay
      if(arrival[n] > latest || !pred.has_value())
      {
        const auto w = boolbv_width.get_width_opt(node.type);
        irep_idt operation = node.id, name;
        if(node.id == ID_fastppa_register || node.id == ID_fastppa_input)
        {
          operation = node.id == ID_fastppa_register ? "register" : "input";
          if(node.value.id() == ID_symbol)
            name = to_symbol_expr(node.value).get_identifier();
        }
        reversed.push_back(
          {operation, name, w.value_or(0), arrival[n], node.source_location});
      }
      if(!pred.has_value())
        break;
      n = *pred;
    }
    steps.assign(reversed.rbegin(), reversed.rend());
  }

  void mark_live()
  {
    live.assign(graph.nodes.size(), false);
    std::vector<std::size_t> stack{graph.outputs.begin(), graph.outputs.end()};

    std::unordered_map<std::size_t, irep_idt> register_name;
    for(auto &[name, n] : graph.register_node)
      register_name[n] = name;

    while(!stack.empty())
    {
      auto n = stack.back();
      stack.pop_back();
      if(live[n])
        continue;
      live[n] = true;
      for(auto op : graph.nodes[n].ops)
        stack.push_back(op);
      if(graph.nodes[n].id == ID_fastppa_register)
      {
        auto ns_it = graph.next_state.find(register_name.at(n));
        if(ns_it != graph.next_state.end())
          stack.push_back(ns_it->second);
      }
    }
  }

  void count_fanout()
  {
    fanout.assign(graph.nodes.size(), 0);
    for(std::size_t n = 0; n < graph.nodes.size(); ++n)
      if(live[n])
        for(auto op : graph.nodes[n].ops)
          ++fanout[op];
    // endpoints count as uses
    for(auto n : graph.outputs)
      ++fanout[n];
    for(auto &[name, n] : graph.next_state)
      ++fanout[n];
  }

  // Is n part of a chain rooted at its single user?
  std::vector<int> absorbed_cache;
  bool absorbed(std::size_t n)
  {
    if(absorbed_cache.empty())
    {
      absorbed_cache.assign(graph.nodes.size(), 0);
      for(std::size_t p = 0; p < graph.nodes.size(); ++p)
      {
        if(!live[p] || !is_associative(graph.nodes[p].id))
          continue;
        for(auto c : graph.nodes[p].ops)
          if(absorbable(p, c))
            absorbed_cache[c] = 1;
      }
      for(std::size_t p = 0; p < graph.nodes.size(); ++p)
        if(live[p] && aligned_select(p).has_value())
          absorbed_cache[graph.nodes[p].ops[0]] = 1;
    }
    return absorbed_cache[n] != 0;
  }

  /// Is node n a constant with exactly one bit set?
  bool is_power_of_two(std::size_t n) const
  {
    const auto &node = graph.nodes[n];
    if(node.id != ID_constant || !can_cast_type<bitvector_typet>(node.type))
      return false;
    const std::size_t w = to_bitvector_type(node.type).get_width();
    const auto &value = to_constant_expr(node.value).get_value();
    std::size_t ones = 0;
    for(std::size_t i = 0; i < w; ++i)
      ones += get_bvrep_bit(value, w, i) ? 1 : 0;
    return ones == 1;
  }

  /// A lower bound for the number of low bits of node n that are zero.
  std::size_t known_zero_low_bits(std::size_t n, unsigned depth = 0) const
  {
    const auto &node = graph.nodes[n];
    if(depth > 8 || !can_cast_type<bitvector_typet>(node.type))
      return 0;
    const std::size_t w = to_bitvector_type(node.type).get_width();
    if(node.id == ID_constant)
    {
      const auto &value = to_constant_expr(node.value).get_value();
      std::size_t k = 0;
      while(k < w && !get_bvrep_bit(value, w, k))
        ++k;
      return k;
    }
    else if(node.id == ID_mult)
    {
      std::size_t k = 0;
      for(auto op : node.ops)
        k += known_zero_low_bits(op, depth + 1);
      return std::min(k, w);
    }
    else if(node.id == ID_shl && graph.is_constant(node.ops[1]))
    {
      auto s = numeric_cast<mp_integer>(graph.nodes[node.ops[1]].value);
      if(!s.has_value())
        return 0;
      return std::min(
        w,
        known_zero_low_bits(node.ops[0], depth + 1) +
          numeric_cast_v<std::size_t>(*s));
    }
    else if(
      node.id == ID_plus || node.id == ID_minus || node.id == ID_bitor ||
      node.id == ID_bitxor)
    {
      std::size_t k = w;
      for(auto op : node.ops)
        k = std::min(k, known_zero_low_bits(op, depth + 1));
      return k;
    }
    else if(node.id == ID_bitand)
    {
      std::size_t k = 0;
      for(auto op : node.ops)
        k = std::max(k, known_zero_low_bits(op, depth + 1));
      return k;
    }
    else if(node.id == ID_typecast || node.id == ID_zero_extend)
      return std::min(w, known_zero_low_bits(node.ops[0], depth + 1));
    return 0;
  }

  /// x[lo +: ow] of x >> d, where d is a multiple of 2^k and the
  /// selected bits lie within one 2^k-bit slot: each output bit is a mux
  /// of the w/2^k bits at its position in each slot. Returns the number
  /// of slots.
  std::optional<std::size_t> aligned_select(std::size_t n) const
  {
    const auto &node = graph.nodes[n];
    if(node.id != ID_extractbits || !graph.is_constant(node.ops[1]))
      return {};
    const auto shift = node.ops[0];
    const auto &s = graph.nodes[shift];
    if(s.id != ID_lshr || graph.is_constant(s.ops[1]) || fanout[shift] != 1)
      return {};
    auto lo = numeric_cast<mp_integer>(graph.nodes[node.ops[1]].value);
    if(!lo.has_value() || !can_cast_type<bitvector_typet>(node.type))
      return {};
    const std::size_t k = known_zero_low_bits(s.ops[1]);
    if(k == 0 || k >= 8 * sizeof(std::size_t))
      return {};
    const std::size_t slot = std::size_t{1} << k;
    const std::size_t ow = to_bitvector_type(node.type).get_width();
    if(numeric_cast_v<std::size_t>(*lo) + ow > slot)
      return {};
    const std::size_t w = to_bitvector_type(s.type).get_width();
    return (w + slot - 1) / slot;
  }

  /// Is node x the array m with some elements written, possibly under
  /// conditions?
  bool is_write_of(std::size_t x, std::size_t m, unsigned depth = 0) const
  {
    if(depth > 64)
      return false;
    const auto &node = graph.nodes[x];
    if(node.id == ID_with && node.type.id() == ID_array)
      return node.ops[0] == m || is_write_of(node.ops[0], m, depth + 1);
    if(node.id == ID_if)
      return (node.ops[1] == m && is_write_of(node.ops[2], m, depth + 1)) ||
             (node.ops[2] == m && is_write_of(node.ops[1], m, depth + 1));
    return false;
  }

  bool absorbable(std::size_t parent, std::size_t child) const
  {
    const auto &p = graph.nodes[parent], &c = graph.nodes[child];
    return c.id == p.id && c.type == p.type && fanout[child] == 1;
  }

  void leaves(std::size_t n, std::vector<std::size_t> &dest) const
  {
    for(auto c : graph.nodes[n].ops)
      if(absorbable(n, c))
        leaves(c, dest);
      else
        dest.push_back(c);
  }

  double max_arrival(const std::vector<std::size_t> &ops) const
  {
    double a = 0;
    for(auto op : ops)
      a = std::max(a, arrival[op]);
    return a;
  }

  std::size_t max_depth(const std::vector<std::size_t> &ops) const
  {
    std::size_t d = 0;
    for(auto op : ops)
      d = std::max(d, depth[op]);
    return d;
  }

  // count operators of the given kind
  void add_cost(
    const std::string &kind,
    std::size_t w,
    std::size_t n,
    std::size_t count = 1,
    double fraction = 1)
  {
    const auto &f = table(kind);
    const double area = fraction * count * f.area(w, n);
    result.combinational_area_um2 += area;
    result.data_energy_fj += fraction * count * f.energy(w, n);
    result.leakage_uw += fraction * count * f.leakage(w, n);
    result.operator_count += count;
    auto &entry = area_by_kind[kind];
    entry.first += count;
    entry.second += area;
  }

  // n is a free node (wiring)
  void free_node(std::size_t n, const std::vector<std::size_t> &ops)
  {
    arrival[n] = max_arrival(ops);
    depth[n] = max_depth(ops);
  }

  // n is one operator of the given kind
  void simple_node(
    std::size_t n,
    const std::string &kind,
    std::size_t w,
    std::size_t size,
    const std::vector<std::size_t> &ops)
  {
    const auto &f = table(kind);
    add_cost(kind, w, size);
    arrival[n] = max_arrival(ops) + f.delay(w, size);
    depth[n] = max_depth(ops) + 1;
  }

  // n-ary associative operator as an arrival-balanced tree of k-1 operators
  void tree_node(
    std::size_t n,
    const std::string &kind,
    std::size_t w,
    const std::vector<std::size_t> &ops)
  {
    if(ops.size() <= 1 || w == 0)
    {
      free_node(n, ops);
      return;
    }
    const auto &f = table(kind);
    add_cost(kind, w, 0, ops.size() - 1);
    const double d = f.delay(w, 0);
    using itemt = std::pair<double, std::size_t>; // arrival, depth
    std::priority_queue<itemt, std::vector<itemt>, std::greater<itemt>> q;
    for(auto op : ops)
      q.push({arrival[op], depth[op]});
    while(q.size() > 1)
    {
      auto a = q.top();
      q.pop();
      auto b = q.top();
      q.pop();
      q.push(
        {std::max(a.first, b.first) + d, std::max(a.second, b.second) + 1});
    }
    arrival[n] = q.top().first;
    depth[n] = q.top().second;
  }

  // bits of a constant that do not decide the result of a bitwise operator
  std::size_t
  undecided_bits(const irep_idt &id, const exprt &constant, std::size_t w) const
  {
    if(constant.is_true())
      return id == ID_and ? 1 : 0;
    if(constant.is_false())
      return id == ID_or ? 1 : 0;
    const auto &value = to_constant_expr(constant).get_value();
    std::size_t ones = 0;
    for(std::size_t i = 0; i < w; ++i)
      if(get_bvrep_bit(value, w, i))
        ++ones;
    if(id == ID_bitand || id == ID_and)
      return ones;
    if(id == ID_bitor || id == ID_or)
      return w - ones;
    return w; // xor: every bit still depends on the other operands
  }

  void cost_associative(std::size_t n)
  {
    const auto &node = graph.nodes[n];
    std::vector<std::size_t> all, non_constant, constant;
    leaves(n, all);
    for(auto l : all)
      (graph.is_constant(l) ? constant : non_constant).push_back(l);

    const bool logic =
      node.id == ID_and || node.id == ID_or || node.id == ID_xor;
    const std::size_t w = logic ? 1 : width(node.type);

    if(node.id == ID_plus || node.id == ID_mult)
    {
      const std::string kind = node.id == ID_plus ? "plus" : "mult";
      tree_node(n, kind, w, non_constant);
      // multiplying by a power of two is wiring
      const bool power_of_two = node.id == ID_mult && constant.size() == 1 &&
                                is_power_of_two(constant[0]);
      if(!constant.empty() && !power_of_two)
      {
        const auto &f = table(kind + "_c");
        add_cost(kind + "_c", w, 0);
        arrival[n] += f.delay(w, 0);
        depth[n] += 1;
      }
      return;
    }

    const irep_idt bit_id = node.id == ID_and   ? ID_bitand
                            : node.id == ID_or  ? ID_bitor
                            : node.id == ID_xor ? ID_bitxor
                                                : node.id;
    std::size_t effective = w;
    for(auto c : constant)
      effective =
        std::min(effective, undecided_bits(node.id, graph.nodes[c].value, w));
    tree_node(n, id2string(bit_id), effective, non_constant);
    if((node.id == ID_bitxor || node.id == ID_xor) && !constant.empty())
    {
      // inverters for the one bits of the constant
      std::size_t ones = 0;
      for(auto c : constant)
        ones += w - undecided_bits(ID_bitor, graph.nodes[c].value, w);
      if(ones != 0)
      {
        add_cost("bitnot", ones, 0);
        arrival[n] += table("bitnot").delay(ones, 0);
      }
    }
  }

  void cost_node(std::size_t n)
  {
    const auto &node = graph.nodes[n];
    const auto &id = node.id;
    const auto &ops = node.ops;

    auto op_width = [this, &ops](std::size_t i)
    { return width(graph.nodes[ops[i]].type); };
    auto any_constant = [this, &ops]()
    {
      return std::any_of(
        ops.begin(),
        ops.end(),
        [this](std::size_t o) { return graph.is_constant(o); });
    };

    if(is_associative(id))
      return cost_associative(n);

    if(id == ID_minus)
    {
      if(any_constant())
        return simple_node(n, "plus_c", width(node.type), 0, ops);
      return simple_node(n, "minus", width(node.type), 0, ops);
    }
    else if(id == ID_unary_minus)
      return simple_node(n, "unary_minus", width(node.type), 0, ops);
    else if(id == ID_div || id == ID_mod)
      return simple_node(
        n, id == ID_div ? "div" : "mod", width(node.type), 0, ops);
    else if(id == ID_bitnot || id == ID_not)
      return simple_node(n, "bitnot", width(node.type), 0, ops);
    else if(id == ID_bitnand || id == ID_bitnor || id == ID_bitxnor)
    {
      const std::string kind = id == ID_bitnand  ? "bitand"
                               : id == ID_bitnor ? "bitor"
                                                 : "bitxor";
      return simple_node(n, kind, width(node.type), 0, ops);
    }
    else if(id == ID_nand || id == ID_nor || id == ID_xnor)
    {
      const irep_idt bit_id = id == ID_nand  ? ID_bitand
                              : id == ID_nor ? ID_bitor
                                             : ID_bitxor;
      return tree_node(n, id2string(bit_id), 1, ops);
    }
    else if(id == ID_implies)
      return simple_node(n, "bitor", 1, 0, ops);
    else if(id == ID_equal || id == ID_notequal)
    {
      if(graph.nodes[ops[0]].type.id() == ID_bool)
        return simple_node(n, "bitxor", 1, 0, ops);
      return simple_node(
        n, any_constant() ? "equal_c" : "equal", op_width(0), 0, ops);
    }
    else if(id == ID_lt || id == ID_le || id == ID_gt || id == ID_ge)
      return simple_node(
        n, any_constant() ? "lt_c" : "lt", op_width(0), 0, ops);
    else if(id == ID_if)
    {
      // a mux with a constant data input is an AND or OR gate per bit
      if(graph.is_constant(ops[1]) || graph.is_constant(ops[2]))
        return simple_node(n, "bitand", width(node.type), 0, ops);
      // A conditional write c ? m WITH i:=v : m is a write whose enable
      // is gated with c: one AND gate per element, not a mux over the
      // whole array.
      if(
        node.type.id() == ID_array &&
        (is_write_of(n, ops[2]) || is_write_of(n, ops[1])))
      {
        auto size = numeric_cast<mp_integer>(to_array_type(node.type).size());
        if(size.has_value())
          return simple_node(
            n, "bitand", numeric_cast_v<std::size_t>(*size), 0, ops);
      }
      return simple_node(n, "if", width(node.type), 0, ops);
    }
    else if(
      id == ID_shl || id == ID_lshr || id == ID_ashr || id == ID_rol ||
      id == ID_ror)
    {
      if(graph.is_constant(ops[1]))
        return free_node(n, ops);
      const std::string kind = id == ID_rol   ? "shl"
                               : id == ID_ror ? "lshr"
                                              : id2string(id);
      // A barrel shifter has one stage per bit of the distance that is
      // not known to be zero.
      const std::size_t w = op_width(0);
      const std::size_t stages = static_cast<std::size_t>(
        std::ceil(std::log2(std::max<std::size_t>(w, 2))));
      const std::size_t k = std::min(known_zero_low_bits(ops[1]), stages - 1);
      if(k == 0)
        return simple_node(n, kind, w, 0, ops);
      const double fraction = double(stages - k) / stages;
      const auto &f = table(kind);
      add_cost(kind, w, 0, 1, fraction);
      arrival[n] = max_arrival(ops) + fraction * f.delay(w);
      depth[n] = max_depth(ops) + 1;
      return;
    }
    else if(id == ID_extractbit)
    {
      if(graph.is_constant(ops[1]))
        return free_node(n, ops);
      return simple_node(n, "index", 1, op_width(0), ops);
    }
    else if(id == ID_extractbits)
    {
      if(auto slots = aligned_select(n))
      {
        // the operands of the absorbed shift
        const auto &shift_ops = graph.nodes[ops[0]].ops;
        return simple_node(
          n,
          "index",
          to_bitvector_type(node.type).get_width(),
          *slots,
          shift_ops);
      }
      if(graph.is_constant(ops[1]))
        return free_node(n, ops);
      return simple_node(n, "lshr", op_width(0), 0, ops);
    }
    else if(id == ID_index)
    {
      if(graph.is_constant(ops[1]))
        return free_node(n, ops);
      auto &array_type = to_array_type(graph.nodes[ops[0]].type);
      auto size = numeric_cast<mp_integer>(array_type.size());
      if(!size.has_value())
        throw ebmc_errort{} << "array of non-constant size";
      return simple_node(
        n,
        "index",
        width(array_type.element_type()),
        numeric_cast_v<std::size_t>(*size),
        ops);
    }
    else if(id == ID_with)
    {
      if(node.type.id() != ID_array)
        return free_node(n, ops);
      auto &array_type = to_array_type(node.type);
      auto size = numeric_cast<mp_integer>(array_type.size());
      if(!size.has_value())
        throw ebmc_errort{} << "array of non-constant size";
      const auto w = width(array_type.element_type());
      const auto s = numeric_cast_v<std::size_t>(*size);
      arrival[n] = max_arrival(ops);
      depth[n] = max_depth(ops);
      double extra = 0;
      // operands: old, index, value, index, value, ...
      for(std::size_t i = 1; i + 1 < ops.size(); i += 2)
      {
        if(graph.is_constant(ops[i]))
          continue;
        const auto &f = table("with");
        add_cost("with", w, s);
        extra = std::max(extra, f.delay(w, s));
      }
      arrival[n] += extra;
      depth[n] += extra > 0 ? 1 : 0;
      return;
    }
    else if(id == ID_typecast)
    {
      if(node.type.id() == ID_bool && graph.nodes[ops[0]].type.id() != ID_bool)
        return simple_node(n, "reduction_or", op_width(0), 0, ops);
      return free_node(n, ops);
    }
    else if(
      id == ID_reduction_and || id == ID_reduction_nand ||
      id == ID_reduction_or || id == ID_reduction_nor ||
      id == ID_reduction_xor || id == ID_reduction_xnor)
    {
      const std::string kind =
        (id == ID_reduction_and || id == ID_reduction_nand) ? "reduction_and"
        : (id == ID_reduction_or || id == ID_reduction_nor) ? "reduction_or"
                                                            : "reduction_xor";
      return simple_node(n, kind, op_width(0), 0, ops);
    }
    else if(
      id == ID_concatenation || id == ID_zero_extend ||
      id == ID_fastppa_assemble || id == ID_struct || id == ID_member ||
      id == ID_array || id == ID_array_of || id == ID_replication ||
      id == ID_union || id == ID_bswap)
    {
      return free_node(n, ops);
    }
    else
      throw ebmc_errort{} << "fastppa --graph: unsupported operator " << id;
  }
};
} // namespace

estimation_resultt estimate(
  const transt &trans,
  const std::vector<symbol_exprt> &state_vars,
  const std::vector<symbol_exprt> &outputs,
  const namespacet &ns,
  const cost_tablet &table,
  message_handlert &message_handler)
{
  messaget message{message_handler};

  // Registers whose next state is a constant, or the register itself, are
  // constants. Finding one can make others constant; iterate.
  std::unordered_map<irep_idt, exprt> constant_registers;
  for(std::size_t iteration = 0;; ++iteration)
  {
    grapht graph{
      trans, state_vars, outputs, ns, constant_registers, message_handler};
    graph.build();

    bool changed = false;
    for(auto &[name, n] : graph.next_state)
    {
      auto r_it = graph.register_node.find(name);
      if(graph.is_constant(n))
      {
        constant_registers.emplace(name, graph.nodes[n].value);
        changed = true;
      }
      else if(r_it != graph.register_node.end() && r_it->second == n)
      {
        constant_registers.emplace(name, nil_exprt{});
        changed = true;
      }
    }
    // registers without a next-state function are never updated
    for(auto &[name, n] : graph.register_node)
      if(graph.next_state.find(name) == graph.next_state.end())
        if(constant_registers.emplace(name, nil_exprt{}).second)
          changed = true;

    if(changed && iteration < 16)
      continue;

    if(graph.undriven_symbols != 0)
      message.warning() << graph.undriven_symbols
                        << " undriven signals treated as constants"
                        << messaget::eom;

    costert coster{graph, table, ns};
    auto result = coster.run();

    message.statistics() << "Graph: " << graph.nodes.size() << " nodes, "
                         << constant_registers.size() << " constant registers"
                         << messaget::eom;
    for(auto &[kind, entry] : coster.area_by_kind)
      message.statistics() << "  " << kind << ": " << entry.first
                           << " operators, " << entry.second << " um2"
                           << messaget::eom;
    return result;
  }
}
