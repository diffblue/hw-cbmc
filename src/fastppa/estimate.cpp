/*******************************************************************\

Module: FastPPA Estimation Engine

Author: Kiro

\*******************************************************************/

#include "estimate.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/mathematical_types.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <verilog/verilog_bits.h>

#include <map>
#include <optional>
#include <unordered_map>
#include <unordered_set>

// --- Named constants for synthesis heuristic factors ---
static constexpr double MULTI_INPUT_GATE_FACTOR = 0.7;
static constexpr double INCREMENTER_FACTOR = 0.6;
static constexpr double MUX_TREE_MIN_DISCOUNT = 0.3;
static constexpr double CMP_CONSTANT_FACTOR = 0.5;
static constexpr double OPERATOR_MERGE_FACTOR = 0.75;

/// Compute the total bit-width of a type, including arrays, structs and
/// (packed) unions.
static std::size_t get_width(const typet &type)
{
  auto bits_opt = verilog_bits_opt(type);
  if(bits_opt.has_value())
    return bits_opt->to_ulong();
  return 1;
}

/// Collect wire definitions from the invariant (invar) constraint.
/// The invariant is a conjunction of equalities: wire_symbol = expr.
static void collect_invar_defs(
  const exprt &invar,
  std::unordered_map<irep_idt, exprt, irep_id_hash> &defs)
{
  if(invar.id() == ID_and)
  {
    for(const auto &op : invar.operands())
      collect_invar_defs(op, defs);
  }
  else if(invar.id() == ID_equal)
  {
    auto &eq = to_equal_expr(invar);
    if(eq.lhs().id() == ID_symbol)
      defs[to_symbol_expr(eq.lhs()).get_identifier()] = eq.rhs();
    else if(eq.rhs().id() == ID_symbol)
      defs[to_symbol_expr(eq.rhs()).get_identifier()] = eq.lhs();
  }
}

/// Pre-resolve invar symbols that transitively evaluate to constants.
/// Populates resolved_constants with symbol_id -> constant_expr mappings.
static void resolve_invar_constants(
  const std::unordered_map<irep_idt, exprt, irep_id_hash> &invar_defs,
  std::unordered_map<irep_idt, exprt, irep_id_hash> &resolved_constants)
{
  for(const auto &[id, def] : invar_defs)
  {
    exprt cur = def;
    std::unordered_set<irep_idt, irep_id_hash> visited;
    visited.insert(id);
    // Follow symbol chains through typecasts
    while(true)
    {
      while(cur.id() == ID_typecast && cur.operands().size() == 1)
        cur = cur.operands()[0];
      if(cur.id() == ID_constant)
      {
        resolved_constants[id] = cur;
        break;
      }
      if(cur.id() == ID_symbol)
      {
        auto &sym_id = to_symbol_expr(cur).get_identifier();
        if(visited.count(sym_id))
          break;
        visited.insert(sym_id);
        auto it = invar_defs.find(sym_id);
        if(it != invar_defs.end())
          cur = it->second;
        else
          break;
      }
      else
        break;
    }
  }
}

/// Apply synthesis heuristic corrections to the raw operator cost.
static void apply_optimizations(
  operator_costt &op_cost,
  const exprt &expr,
  std::size_t width,
  std::size_t max_child_depth,
  bool cmp_against_constant,
  const std::unordered_map<irep_idt, exprt, irep_id_hash> &invar_defs,
  const std::unordered_map<irep_idt, exprt, irep_id_hash> &resolved_constants,
  const technology_dbt &tech)
{
  // Helper: check if an operand resolves to a constant via invar or
  // pre-resolved constants.
  auto operand_is_constant = [&](const exprt &op) -> bool
  {
    if(op.id() == ID_constant)
      return true;
    if(op.id() == ID_symbol)
    {
      auto &sym_id = to_symbol_expr(op).get_identifier();
      if(resolved_constants.count(sym_id))
        return true;
      auto def = invar_defs.find(sym_id);
      if(def != invar_defs.end() && def->second.id() == ID_constant)
        return true;
    }
    return false;
  };

  // Multi-input gate correction.
  if(expr.operands().size() >= 3 && op_cost.area_um2 > 0)
  {
    op_cost.area_um2 *= MULTI_INPUT_GATE_FACTOR;
    op_cost.energy_fj *= MULTI_INPUT_GATE_FACTOR;
  }

  // Constant operand strength reduction for add/sub.
  if(
    (expr.id() == ID_plus || expr.id() == ID_minus) &&
    expr.operands().size() == 2)
  {
    bool has_const = operand_is_constant(expr.operands()[0]) ||
                     operand_is_constant(expr.operands()[1]);
    if(has_const)
    {
      op_cost.area_um2 *= INCREMENTER_FACTOR;
      op_cost.energy_fj *= INCREMENTER_FACTOR;
    }
  }

  // MUX-tree cost for case/if-chains.
  if(expr.id() == ID_if && max_child_depth > 2)
  {
    double depth_discount =
      std::sqrt(2.0 / static_cast<double>(max_child_depth));
    if(depth_discount < MUX_TREE_MIN_DISCOUNT)
      depth_discount = MUX_TREE_MIN_DISCOUNT;
    op_cost.area_um2 *= depth_discount;
    op_cost.energy_fj *= depth_discount;
  }

  // Comparison against zero/constant: much cheaper (NOR/XOR reduction)
  if(cmp_against_constant && op_cost.area_um2 > 0)
  {
    op_cost.area_um2 *= CMP_CONSTANT_FACTOR;
    op_cost.energy_fj *= CMP_CONSTANT_FACTOR;
  }

  // Narrow signal floor: 1-bit operations cost at most 1 gate
  if(
    width <= 1 &&
    op_cost.area_um2 > 3.0 * tech.operator_cost(ID_bitand, 1).area_um2)
  {
    op_cost.area_um2 = tech.operator_cost(ID_bitand, 1).area_um2;
    op_cost.energy_fj = tech.operator_cost(ID_bitand, 1).energy_fj;
  }

  // Operator merging: consecutive same-type ops.
  if(
    (expr.id() == ID_plus || expr.id() == ID_bitxor || expr.id() == ID_bitor ||
     expr.id() == ID_bitand) &&
    expr.operands().size() == 2)
  {
    bool child_same_op = false;
    for(const auto &op : expr.operands())
    {
      if(op.id() == expr.id())
      {
        child_same_op = true;
        break;
      }
    }
    if(child_same_op)
    {
      op_cost.area_um2 *= OPERATOR_MERGE_FACTOR;
      op_cost.energy_fj *= OPERATOR_MERGE_FACTOR;
    }
  }
}

/// Check if a binary expression is an identity/absorbing operation
/// (e.g. x+0, x*1, x*0, x&all_ones) that synthesizes for free.
static bool is_identity_op(const exprt &expr)
{
  auto is_zero = [](const exprt &e) { return e == 0; };
  auto is_all_ones = [](const exprt &e)
  {
    if(e.id() != ID_constant)
      return false;
    mp_integer val;
    if(to_integer(to_constant_expr(e), val))
      return false;
    if(val == -1)
      return true; // signed all-ones
    auto width_opt = verilog_bits_opt(e.type());
    if(!width_opt.has_value() || width_opt->is_zero())
      return false;
    return val == power(mp_integer(2), *width_opt) - 1;
  };
  auto is_one = [](const exprt &e) { return e == 1; };

  const auto &op0 = expr.operands()[0];
  const auto &op1 = expr.operands()[1];

  if(
    expr.id() == ID_plus || expr.id() == ID_minus || expr.id() == ID_bitor ||
    expr.id() == ID_bitxor || expr.id() == ID_shl || expr.id() == ID_lshr ||
    expr.id() == ID_ashr)
  {
    if(is_zero(op1))
      return true;
  }
  if(expr.id() == ID_plus && is_zero(op0))
    return true;
  if(expr.id() == ID_mult && (is_one(op0) || is_one(op1)))
    return true;
  if(expr.id() == ID_mult && (is_zero(op0) || is_zero(op1)))
    return true;
  if(expr.id() == ID_bitand && (is_all_ones(op0) || is_all_ones(op1)))
    return true;
  return false;
}

/// Check if a comparison has a constant operand (directly or via resolved).
static bool is_cmp_against_constant(
  const exprt &expr,
  const std::unordered_map<irep_idt, exprt, irep_id_hash> &resolved_constants)
{
  if(
    !(expr.id() == ID_equal || expr.id() == ID_notequal || expr.id() == ID_lt ||
      expr.id() == ID_le || expr.id() == ID_gt || expr.id() == ID_ge) ||
    expr.operands().size() != 2)
    return false;

  for(const auto &op : expr.operands())
  {
    if(op.id() == ID_constant)
      return true;
    if(
      op.id() == ID_symbol &&
      resolved_constants.count(to_symbol_expr(op).get_identifier()))
      return true;
  }
  return false;
}

/// Resolve an expression to a constant through typecasts and invar defs.
static std::optional<exprt> resolve_to_constant(
  const exprt &e,
  const std::unordered_map<irep_idt, exprt, irep_id_hash> &invar_defs,
  const std::unordered_map<irep_idt, exprt, irep_id_hash> &resolved_constants)
{
  exprt cur = e;
  while(cur.id() == ID_typecast && cur.operands().size() == 1)
    cur = cur.operands()[0];
  if(cur.id() == ID_constant)
    return cur;
  if(cur.id() == ID_symbol)
  {
    auto &sym_id = to_symbol_expr(cur).get_identifier();
    auto rc = resolved_constants.find(sym_id);
    if(rc != resolved_constants.end())
      return rc->second;
    auto it = invar_defs.find(sym_id);
    if(it != invar_defs.end())
    {
      cur = it->second;
      while(cur.id() == ID_typecast && cur.operands().size() == 1)
        cur = cur.operands()[0];
      if(cur.id() == ID_constant)
        return cur;
    }
  }
  return std::nullopt;
}

/// Compute the base operator cost for an expression node.
static operator_costt cost_operator(
  const exprt &expr,
  std::size_t width,
  const std::unordered_map<irep_idt, exprt, irep_id_hash> &invar_defs,
  const std::unordered_map<irep_idt, exprt, irep_id_hash> &resolved_constants,
  const technology_dbt &tech)
{
  if(expr.id() == ID_mult && expr.operands().size() == 2)
  {
    auto const_op =
      resolve_to_constant(expr.operands()[0], invar_defs, resolved_constants);
    if(!const_op)
      const_op =
        resolve_to_constant(expr.operands()[1], invar_defs, resolved_constants);

    if(const_op.has_value())
    {
      mp_integer value;
      if(!to_integer(to_constant_expr(*const_op), value))
      {
        if(value < 0)
          value += power(mp_integer(2), get_width(const_op->type()));
        std::size_t set_bits = 0;
        while(value > 0)
        {
          if(value % 2 != 0)
            set_bits++;
          value /= 2;
        }
        if(set_bits == 0)
          set_bits = 1;
        return tech.constant_mult_cost(width, set_bits);
      }
    }
    return tech.operator_cost(ID_mult, width);
  }

  if(expr.id() == ID_index)
  {
    // A constant index selects a fixed element at synthesis time -- it's
    // direct wiring to that element's bits, not a decoder/mux tree, so it
    // has no hardware cost of its own (the array_size:1 mux only exists
    // when the index is a runtime signal).
    auto &index_op = expr.operands()[1];
    if(
      index_op.id() == ID_constant ||
      resolve_to_constant(index_op, invar_defs, resolved_constants))
      return operator_costt{};

    auto &array_op = expr.operands()[0];
    std::size_t array_size = 32;
    if(array_op.type().id() == ID_array)
    {
      auto &atype = to_array_type(array_op.type());
      if(atype.size().id() == ID_constant)
      {
        auto sz = numeric_cast_v<mp_integer>(to_constant_expr(atype.size()));
        if(sz > 0)
          array_size = sz.to_ulong();
      }
    }
    return tech.index_cost(width, array_size);
  }

  return tech.operator_cost(expr.id(), width);
}

/// Recursively walk expression DAG, resolving symbol references through
/// invariant definitions, accumulating costs.
/// Uses structural equality (exprt::operator==) for caching to detect sharing.
static node_costt walk_expr(
  const exprt &expr,
  std::map<exprt, node_costt> &cache,
  std::unordered_set<irep_idt, irep_id_hash> &resolving,
  std::unordered_set<irep_idt, irep_id_hash> &visited_invar_symbols,
  const std::unordered_map<irep_idt, exprt, irep_id_hash> &invar_defs,
  const std::unordered_map<irep_idt, exprt, irep_id_hash> &resolved_constants,
  double &total_area,
  double &total_energy,
  std::size_t &op_count,
  const technology_dbt &tech)
{
  // Check structural cache
  auto it = cache.find(expr);
  if(it != cache.end())
    return it->second;

  // If this is a symbol reference and we have a definition for it,
  // follow through to the defining expression (with cycle detection).
  if(expr.id() == ID_symbol)
  {
    auto &id = to_symbol_expr(expr).get_identifier();
    auto def_it = invar_defs.find(id);
    if(def_it != invar_defs.end() && resolving.find(id) == resolving.end())
    {
      // Mark as visited for cross-NSF sharing detection.
      // If already visited by a *previous* NSF, skip area (shared wire).
      bool already_costed = visited_invar_symbols.count(id) > 0;

      resolving.insert(id);
      double saved_area = total_area;
      double saved_energy = total_energy;
      std::size_t saved_ops = op_count;
      auto result = walk_expr(
        def_it->second,
        cache,
        resolving,
        visited_invar_symbols,
        invar_defs,
        resolved_constants,
        total_area,
        total_energy,
        op_count,
        tech);
      resolving.erase(id);
      // Mark as visited *after* walk completes, so child aliases within
      // the same walk don't see their parent as "already costed".
      visited_invar_symbols.insert(id);
      // If this wire was already costed by a previous NSF, undo area
      if(already_costed)
      {
        total_area = saved_area;
        total_energy = saved_energy;
        op_count = saved_ops;
      }
      cache[expr] = result;
      return result;
    }
    // Primary input, unresolved, or cyclic — zero cost leaf
    node_costt cost;
    cache[expr] = cost;
    return cost;
  }

  // Leaf nodes: constants
  if(expr.operands().empty())
  {
    node_costt cost;
    cache[expr] = cost;
    return cost;
  }

  // --- Synthesis optimizations: detect zero-cost patterns ---

  // Constant folding: all operands are constants (or resolve to constants)
  // → result is constant, free
  {
    bool all_const = true;
    for(const auto &op : expr.operands())
    {
      if(op.id() == ID_constant)
        continue;
      if(
        op.id() == ID_symbol &&
        resolved_constants.count(to_symbol_expr(op).get_identifier()))
        continue;
      all_const = false;
      break;
    }
    if(all_const && !expr.operands().empty())
    {
      node_costt cost;
      cache[expr] = cost;
      return cost;
    }
  }

  // Identity/absorbing operations: zero cost. This node is a pass-through
  // (e.g. x+0 is just x), so propagate the dominant operand's chain
  // bookkeeping unchanged -- otherwise a real chain like (x+0)+c would
  // look to its parent like a fresh 1-leaf node instead of a continuation
  // of x's chain, breaking the associative-chain delay balancing below.
  if(expr.operands().size() == 2 && is_identity_op(expr))
  {
    node_costt dominant;
    for(const auto &op : expr.operands())
    {
      auto child = walk_expr(
        op,
        cache,
        resolving,
        visited_invar_symbols,
        invar_defs,
        resolved_constants,
        total_area,
        total_energy,
        op_count,
        tech);
      if(child.arrival_ps > dominant.arrival_ps)
        dominant = child;
    }
    cache[expr] = dominant;
    return dominant;
  }

  // Dead MUX: if-then-else where both branches are the same
  if(expr.id() == ID_if && expr.operands().size() == 3)
  {
    if(expr.operands()[1] == expr.operands()[2])
    {
      auto child = walk_expr(
        expr.operands()[1],
        cache,
        resolving,
        visited_invar_symbols,
        invar_defs,
        resolved_constants,
        total_area,
        total_energy,
        op_count,
        tech);
      cache[expr] = child;
      return child;
    }
  }

  // Find max arrival from children. Also track, for associative-chain
  // balancing below, which operand is a literal same-op continuation
  // (e.g. the lhs of ((a+b)+c)+d) and what its chain bookkeeping is.
  double max_child_arrival = 0;
  std::size_t max_child_depth = 0;
  // chain_terms counts how many leaf terms this node merges, treating a
  // same-op operand (e.g. the lhs of ((a+b)+c)+d) as already having
  // merged its own chain_length leaves rather than as one opaque operand.
  std::size_t chain_terms = 0;
  double chain_leaf_max_ps = 0;
  bool is_assoc_chain_op = expr.id() == ID_plus || expr.id() == ID_minus ||
                           expr.id() == ID_bitand || expr.id() == ID_bitor ||
                           expr.id() == ID_bitxor;

  for(const auto &op : expr.operands())
  {
    auto child = walk_expr(
      op,
      cache,
      resolving,
      visited_invar_symbols,
      invar_defs,
      resolved_constants,
      total_area,
      total_energy,
      op_count,
      tech);
    if(child.arrival_ps > max_child_arrival)
      max_child_arrival = child.arrival_ps;
    if(child.depth > max_child_depth)
      max_child_depth = child.depth;

    if(is_assoc_chain_op)
    {
      bool same_op_continuation = op.id() == expr.id();
      chain_terms += same_op_continuation ? child.chain_length : 1;
      double leaf =
        same_op_continuation ? child.chain_leaf_max_ps : child.arrival_ps;
      if(leaf > chain_leaf_max_ps)
        chain_leaf_max_ps = leaf;
    }
  }

  // Cost this operator
  std::size_t width = get_width(expr.type());

  // For comparisons, cost depends on operand width, not result (bool)
  if(
    expr.id() == ID_equal || expr.id() == ID_notequal || expr.id() == ID_lt ||
    expr.id() == ID_le || expr.id() == ID_gt || expr.id() == ID_ge)
  {
    width = get_width(to_binary_relation_expr(expr).lhs().type());
  }

  // Reduction operators (e.g. ^data) also collapse to a 1-bit result;
  // the gate count and delay depend on the operand width being reduced.
  if(
    (expr.id() == ID_reduction_and || expr.id() == ID_reduction_or ||
     expr.id() == ID_reduction_xor) &&
    expr.operands().size() == 1)
  {
    width = get_width(expr.operands()[0].type());
  }

  bool cmp_against_constant = is_cmp_against_constant(expr, resolved_constants);

  operator_costt op_cost =
    cost_operator(expr, width, invar_defs, resolved_constants, tech);

  // Apply synthesis heuristic corrections
  apply_optimizations(
    op_cost,
    expr,
    width,
    max_child_depth,
    cmp_against_constant,
    invar_defs,
    resolved_constants,
    tech);

  node_costt result;
  if(is_assoc_chain_op && chain_terms >= 2 && op_cost.delay_ps > 0)
  {
    // A +/-/&/|/^ node merging >=2 leaf terms: model the balanced tree a
    // real synthesizer would restructure an associative chain into
    // (e.g. a sum-of-products ((a+b)+c)+d costs log2(4)=2 stages, not 3),
    // rather than paying the full per-stage delay once per literal
    // nesting level in the original (left- or right-associative) RTL.
    result.chain_length = chain_terms;
    result.chain_leaf_max_ps = chain_leaf_max_ps;
    double tree_levels = std::ceil(std::log2(static_cast<double>(chain_terms)));
    result.arrival_ps = chain_leaf_max_ps + op_cost.delay_ps * tree_levels;
  }
  else
  {
    result.chain_length = 1;
    result.chain_leaf_max_ps = max_child_arrival + op_cost.delay_ps;
    result.arrival_ps = max_child_arrival + op_cost.delay_ps;
  }
  result.area_um2 = op_cost.area_um2;
  result.energy_fj = op_cost.energy_fj;
  result.depth = max_child_depth + (op_cost.delay_ps > 0 ? 1 : 0);

  // Accumulate totals
  total_area += op_cost.area_um2;
  total_energy += op_cost.energy_fj;
  if(op_cost.area_um2 > 0 || op_cost.delay_ps > 0)
    op_count++;

  cache[expr] = result;
  return result;
}

/// Strip identity branches from an FSM if-chain.
/// Returns the non-identity branches that need costing. Also collects the
/// condition expression of every if-level traversed (including those whose
/// then-branch turned out to be identity): the decision/select logic itself
/// still needs to be synthesized regardless of how many branches are
/// no-ops.
static std::vector<exprt> strip_fsm_identity(
  const exprt &resolved,
  const irep_idt &id,
  const std::unordered_map<irep_idt, exprt, irep_id_hash> &invar_defs,
  std::size_t &total_branches,
  std::vector<exprt> &conditions)
{
  std::vector<exprt> active_branches;
  total_branches = 0;
  exprt cur = resolved;

  while(cur.id() == ID_if && cur.operands().size() == 3)
  {
    exprt then_branch = cur.operands()[1];
    exprt else_branch = cur.operands()[2];
    total_branches++;
    conditions.push_back(cur.operands()[0]);

    bool then_is_identity = false;
    if(
      then_branch.id() == ID_symbol &&
      to_symbol_expr(then_branch).get_identifier() == id)
      then_is_identity = true;
    else if(then_branch.id() == ID_symbol)
    {
      auto def = invar_defs.find(to_symbol_expr(then_branch).get_identifier());
      if(
        def != invar_defs.end() && def->second.id() == ID_symbol &&
        to_symbol_expr(def->second).get_identifier() == id)
        then_is_identity = true;
    }

    if(!then_is_identity)
      active_branches.push_back(then_branch);

    cur = std::move(else_branch);
    if(cur.id() == ID_symbol)
    {
      auto def = invar_defs.find(to_symbol_expr(cur).get_identifier());
      if(def != invar_defs.end())
        cur = def->second;
    }
  }

  bool final_is_identity =
    (cur.id() == ID_symbol && to_symbol_expr(cur).get_identifier() == id);
  if(!final_is_identity && !cur.operands().empty())
    active_branches.push_back(cur);

  return active_branches;
}

/// HLS-style operator sharing: walk FSM branches, take max cost.
/// Mutually-exclusive branches share one functional unit (max, not sum),
/// but the select logic that decides which branch's result to commit
/// (condition evaluation + the resulting mux) is real hardware that has to
/// be paid for regardless of how many branches are no-ops.
static void walk_fsm_branches(
  const std::vector<exprt> &active_branches,
  const std::vector<exprt> &conditions,
  std::size_t result_width,
  std::map<exprt, node_costt> &cache,
  std::unordered_set<irep_idt, irep_id_hash> &resolving,
  std::unordered_set<irep_idt, irep_id_hash> &visited_invar_symbols,
  const std::unordered_map<irep_idt, exprt, irep_id_hash> &invar_defs,
  const std::unordered_map<irep_idt, exprt, irep_id_hash> &resolved_constants,
  std::map<exprt, node_costt> &condition_decode_cache,
  double &comb_area,
  double &comb_energy,
  std::size_t &op_count,
  double &max_arrival,
  std::size_t &max_depth,
  const technology_dbt &tech)
{
  double max_branch_area = 0;
  double max_branch_energy = 0;
  std::size_t max_branch_ops = 0;
  double branch_arrival = 0;
  std::size_t branch_depth = 0;
  for(const auto &branch : active_branches)
  {
    double branch_area = 0;
    double branch_energy = 0;
    std::size_t branch_ops = 0;
    auto node = walk_expr(
      branch,
      cache,
      resolving,
      visited_invar_symbols,
      invar_defs,
      resolved_constants,
      branch_area,
      branch_energy,
      branch_ops,
      tech);
    if(branch_area > max_branch_area)
      max_branch_area = branch_area;
    if(branch_energy > max_branch_energy)
      max_branch_energy = branch_energy;
    if(branch_ops > max_branch_ops)
      max_branch_ops = branch_ops;
    if(node.arrival_ps > branch_arrival)
      branch_arrival = node.arrival_ps;
    if(node.depth > branch_depth)
      branch_depth = node.depth;
  }

  // Select logic: every condition is real comparator/decode hardware,
  // and the chosen branch still has to be muxed into the register.
  // The same condition (e.g. a shared FSM state decode such as
  // `state == get_a`) commonly drives the update logic of many different
  // registers; that decoder is one piece of hardware, not one per register,
  // so its area/energy is only paid for the first time it is seen.
  double cond_arrival = 0;
  std::size_t cond_depth = 0;
  for(const auto &cond : conditions)
  {
    auto cached = condition_decode_cache.find(cond);
    if(cached != condition_decode_cache.end())
    {
      if(cached->second.arrival_ps > cond_arrival)
        cond_arrival = cached->second.arrival_ps;
      if(cached->second.depth > cond_depth)
        cond_depth = cached->second.depth;
      continue;
    }

    double cond_area = 0;
    double cond_energy = 0;
    std::size_t cond_ops = 0;
    auto node = walk_expr(
      cond,
      cache,
      resolving,
      visited_invar_symbols,
      invar_defs,
      resolved_constants,
      cond_area,
      cond_energy,
      cond_ops,
      tech);
    condition_decode_cache[cond] = node;
    max_branch_area += cond_area;
    max_branch_energy += cond_energy;
    max_branch_ops += cond_ops;
    if(node.arrival_ps > cond_arrival)
      cond_arrival = node.arrival_ps;
    if(node.depth > cond_depth)
      cond_depth = node.depth;
  }

  if(!conditions.empty())
  {
    auto sel_cost = tech.mux_cost(result_width, conditions.size() + 1);
    max_branch_area += sel_cost.area_um2;
    max_branch_energy += sel_cost.energy_fj;
    max_branch_ops++;
    double select_ready =
      std::max(branch_arrival, cond_arrival) + sel_cost.delay_ps;
    if(select_ready > max_arrival)
      max_arrival = select_ready;
    std::size_t select_depth = std::max(branch_depth, cond_depth) + 1;
    if(select_depth > max_depth)
      max_depth = select_depth;
  }
  else
  {
    if(branch_arrival > max_arrival)
      max_arrival = branch_arrival;
    if(branch_depth > max_depth)
      max_depth = branch_depth;
  }

  comb_area += max_branch_area;
  comb_energy += max_branch_energy;
  op_count += max_branch_ops;
}

/// Accumulate register area and energy into the result.
static void compute_register_costs(
  const std::vector<symbol_exprt> &state_vars,
  const technology_dbt &tech,
  estimation_resultt &result)
{
  for(const auto &var : state_vars)
  {
    std::size_t width = get_width(var.type());
    if(width == 0)
      width = 1;
    result.register_bits += width;

    // SRAM macros only pay off above a few Kbit; smaller arrays (register
    // files, small buffers) are realistically synthesized as flip-flops,
    // confirmed against real synthesis: a 1024-bit (32x32) register file
    // maps to 1088 real DFF_X1 cells, not an SRAM macro.
    if(var.type().id() == ID_array && width > 4096)
    {
      // SRAM density: ~1 µm²/bit at 45nm, scaled by process area factor
      double sram_area = static_cast<double>(width) * 1.0 * tech.area_scale();
      result.register_area_um2 += sram_area;
      result.total_energy_fj +=
        static_cast<double>(width) * 0.5 * tech.energy_scale();
    }
    else
    {
      auto reg_cost = tech.register_cost(width);
      result.register_area_um2 += reg_cost.area_um2;
      result.total_energy_fj += reg_cost.energy_fj;
    }
  }
}

estimation_resultt estimate(
  const word_level_transt &wl_trans,
  const transt &trans_expr,
  const std::vector<symbol_exprt> &state_vars,
  const technology_dbt &tech,
  const namespacet &ns)
{
  estimation_resultt result;

  // Collect wire definitions from invar
  std::unordered_map<irep_idt, exprt, irep_id_hash> invar_defs;
  collect_invar_defs(trans_expr.invar(), invar_defs);

  // Full constant propagation: pre-resolve invar symbols to constants
  std::unordered_map<irep_idt, exprt, irep_id_hash> resolved_constants;
  resolve_invar_constants(invar_defs, resolved_constants);

  // Register costs
  compute_register_costs(state_vars, tech, result);

  // Walk each next-state function
  std::unordered_set<irep_idt, irep_id_hash> resolving;
  std::unordered_set<irep_idt, irep_id_hash> visited_invar_symbols;
  double comb_area = 0;
  double comb_energy = 0;
  std::size_t op_count = 0;
  double total_bits_branches = 0;
  double active_bits_branches = 0;
  double max_arrival = 0;
  std::size_t max_depth = 0;
  // Shared FSM state-decode logic (e.g. `state == get_a`) is one decoder
  // reused by many registers' select muxes, not one decoder per register.
  std::map<exprt, node_costt> condition_decode_cache;

  for(const auto &[id, expr] : wl_trans.next_state_functions)
  {
    // Per-NSF cache prevents structural deduplication across registers.
    // Shared wires are handled via visited_invar_symbols (counted once globally).
    std::map<exprt, node_costt> cache;

    // Resolve the expression through invar if it's a symbol
    exprt resolved = expr;
    bool skip_area = false;
    if(resolved.id() == ID_symbol)
    {
      auto &sym_id = to_symbol_expr(resolved).get_identifier();
      auto def = invar_defs.find(sym_id);
      if(def != invar_defs.end())
      {
        if(visited_invar_symbols.count(sym_id))
          skip_area = true; // shared wire, already costed
        else
          visited_invar_symbols.insert(sym_id);
        resolved = def->second;
      }
    }

    // If this NSF's top symbol was already costed (shared wire),
    // save state so we only get delay, not double-counted area.
    double saved_area = comb_area;
    double saved_energy = comb_energy;
    std::size_t saved_ops = op_count;

    // FSM optimization: if the expression is an if-chain where most
    // branches are identity (var' = var), only walk the non-identity
    // branches. The select logic (conditions + mux) is still costed in
    // walk_fsm_branches regardless of how many branches are identity.
    std::size_t total_branches = 0;
    std::vector<exprt> conditions;
    auto active_branches =
      strip_fsm_identity(resolved, id, invar_defs, total_branches, conditions);

    std::size_t result_width = get_width(expr.type());
    if(result_width == 0)
      result_width = 1;

    // Accumulate activity stats weighted by register width
    if(total_branches > 0)
    {
      total_bits_branches += static_cast<double>(total_branches) * result_width;
      active_bits_branches +=
        static_cast<double>(active_branches.size()) * result_width;
    }

    if(!active_branches.empty())
    {
      walk_fsm_branches(
        active_branches,
        conditions,
        result_width,
        cache,
        resolving,
        visited_invar_symbols,
        invar_defs,
        resolved_constants,
        condition_decode_cache,
        comb_area,
        comb_energy,
        op_count,
        max_arrival,
        max_depth,
        tech);
    }
    else
    {
      // Not an FSM pattern or too few identity branches — walk normally
      auto node = walk_expr(
        resolved,
        cache,
        resolving,
        visited_invar_symbols,
        invar_defs,
        resolved_constants,
        comb_area,
        comb_energy,
        op_count,
        tech);
      if(node.arrival_ps > max_arrival)
        max_arrival = node.arrival_ps;
      if(node.depth > max_depth)
        max_depth = node.depth;
    }

    // Restore area if this was a shared wire (only delay matters)
    if(skip_area)
    {
      comb_area = saved_area;
      comb_energy = saved_energy;
      op_count = saved_ops;
    }
  }

  // For purely combinational designs (no next-state functions),
  // walk the invar definitions directly.
  if(wl_trans.next_state_functions.empty())
  {
    std::map<exprt, node_costt> cache;
    for(const auto &[id, def] : invar_defs)
    {
      auto node = walk_expr(
        def,
        cache,
        resolving,
        visited_invar_symbols,
        invar_defs,
        resolved_constants,
        comb_area,
        comb_energy,
        op_count,
        tech);
      if(node.arrival_ps > max_arrival)
        max_arrival = node.arrival_ps;
      if(node.depth > max_depth)
        max_depth = node.depth;
    }
  }

  // Activity ratio: fraction of logic active per cycle, weighted by bit-width
  double activity_ratio =
    total_bits_branches > 0 ? active_bits_branches / total_bits_branches : 1.0;

  // Cross-register resource sharing: walk_fsm_branches already takes
  // max-not-sum across one register's own mutually-exclusive branches, but
  // an iterative/FSM datapath (e.g. a multi-cycle FP unit) typically reuses
  // the *same* functional units (adders, shifters, ...) across *different*
  // registers' updates in different states too -- that sharing isn't
  // visible to a per-register walk. A low activity ratio (few of the many
  // textual state/register update combinations are live in any one state)
  // is the signature of this pattern. Calibrated against real synthesis
  // (Yosys+ABC, NanGate45) of FSM-based floating-point cores, where
  // activity ratios of 0.28-0.46 corresponded to needing roughly the
  // square of that ratio applied to the combinational area.
  double sharing_factor =
    activity_ratio < 1.0 ? activity_ratio * activity_ratio : 1.0;
  comb_area *= sharing_factor;
  comb_energy *= sharing_factor;

  result.combinational_area_um2 = comb_area;
  result.total_area_um2 = result.register_area_um2 + comb_area;
  result.critical_path_ps = max_arrival;
  result.total_energy_fj += comb_energy;
  result.combinational_depth = max_depth;
  result.operator_count = op_count;
  result.activity_ratio = activity_ratio;

  return result;
}
