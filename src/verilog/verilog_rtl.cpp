/*******************************************************************\

Module: Verilog Register-Transfer Level Representation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_rtl.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/mathematical_types.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table_base.h>

#include <ebmc/ebmc_error.h>

#include "expr2verilog.h"
#include "verilog_expr.h"
#include "verilog_typecheck_base.h"

#include <ostream>
#include <set>

/*******************************************************************\

   Class: verilog_rtl_buildert

 Purpose: Constructs the RTL representation of a module from the
          type-checked module items, before synthesis.

\*******************************************************************/

class verilog_rtl_buildert : public verilog_typecheck_baset
{
public:
  verilog_rtl_buildert(
    verilog_standardt _standard,
    const namespacet &_ns,
    const irep_idt &_module,
    message_handlert &_message_handler)
    : verilog_typecheck_baset(_standard, _ns, _message_handler), module(_module)
  {
  }

  void typecheck() override
  {
  }

  // throws errort on error
  verilog_rtlt build();

protected:
  const irep_idt module;
  verilog_rtlt rtl;

  using kindt = verilog_rtl_definitiont::kindt;

  /// the state while processing the statements of one always construct
  class statet
  {
  public:
    /// values assigned so far, per identifier and slice
    using slice_valuest = std::map<verilog_rtl_slicet, exprt>;
    std::map<irep_idt, slice_valuest> values;

    /// values assigned to entire identifiers by blocking assignments;
    /// these are substituted into subsequent right-hand sides
    std::map<irep_idt, exprt> blocking_values;

    /// identifiers that have a slice-level blocking assignment;
    /// reading these afterwards is not supported
    std::set<irep_idt> partial_blocking;
  };

  /// an lvalue, decomposed into its base symbol and the slice selected
  class lhst
  {
  public:
    symbol_exprt symbol;
    verilog_rtl_slicet slice;

    lhst(symbol_exprt _symbol, verilog_rtl_slicet _slice)
      : symbol(std::move(_symbol)), slice(std::move(_slice))
    {
    }
  };

  // module items
  void build_module_item(const verilog_module_itemt &);
  void build_always(const verilog_always_baset &);
  void build_continuous_assign(const verilog_continuous_assignt &);

  // statements
  void build_statement(const verilog_statementt &, statet &);
  void build_assign(const verilog_assignt &, statet &, bool blocking);
  void build_if(const verilog_ift &, statet &);

  void merge(
    const exprt &cond,
    const statet &then_state,
    const statet &else_state,
    statet &dest);

  lhst decompose_lhs(const exprt &lhs);

  /// the current value of the given slice of the given symbol
  exprt slice_of(const symbol_exprt &, const verilog_rtl_slicet &);

  /// given the value of slice \p from, extract the value of the
  /// sub-slice \p sub
  static exprt extract_range(
    const exprt &value,
    const verilog_rtl_slicet &from,
    const verilog_rtl_slicet &sub);

  /// record the value of a slice, splitting any previously recorded
  /// overlapping slices
  static void
  write_slice(statet::slice_valuest &, const verilog_rtl_slicet &, exprt value);

  /// the value of the given fragment as recorded in the given map,
  /// or the current value of the fragment if not recorded
  exprt fragment_value(
    const statet::slice_valuest &,
    const verilog_rtl_slicet &fragment,
    const symbol_exprt &);

  /// apply the blocking-assignment values to the given rvalue
  exprt substitute(exprt, const statet &);

  void commit(const statet &, kindt, const source_locationt &);

  mp_integer constant_value(const exprt &, const source_locationt &) const;

  /// the width of the entire identifier as a slice
  verilog_rtl_slicet whole_slice(const symbol_exprt &symbol)
  {
    return verilog_rtl_slicet{0, get_width(symbol.type()) - 1};
  }
};

/*******************************************************************\

Function: verilog_rtl_buildert::constant_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer verilog_rtl_buildert::constant_value(
  const exprt &expr,
  const source_locationt &source_location) const
{
  auto value_opt = numeric_cast<mp_integer>(expr);

  if(!value_opt.has_value())
  {
    throw errort().with_location(source_location)
      << "RTL construction requires a constant, but got `" << expr.id() << "'";
  }

  return *value_opt;
}

/*******************************************************************\

Function: verilog_rtl_buildert::decompose_lhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

verilog_rtl_buildert::lhst verilog_rtl_buildert::decompose_lhs(const exprt &lhs)
{
  if(lhs.id() == ID_symbol)
  {
    auto &symbol_expr = to_symbol_expr(lhs);
    return lhst{symbol_expr, whole_slice(symbol_expr)};
  }
  else if(lhs.id() == ID_verilog_bit_select)
  {
    auto &bit_select = to_verilog_bit_select_expr(lhs);
    auto &src = bit_select.src();

    if(src.id() != ID_symbol || src.type().id() == ID_array)
    {
      throw errort().with_location(lhs.source_location())
        << "unsupported lvalue for RTL construction";
    }

    auto index = constant_value(bit_select.index(), lhs.source_location());
    auto offset = mp_integer{src.type().get_int(ID_C_offset)};
    auto bit = index - offset;

    return lhst{to_symbol_expr(src), verilog_rtl_slicet{bit, bit}};
  }
  else if(lhs.id() == ID_verilog_non_indexed_part_select)
  {
    auto &part_select = to_verilog_non_indexed_part_select_expr(lhs);
    auto &src = part_select.src();

    if(src.id() != ID_symbol)
    {
      throw errort().with_location(lhs.source_location())
        << "unsupported lvalue for RTL construction";
    }

    auto from = constant_value(part_select.lsb(), lhs.source_location());
    auto to = constant_value(part_select.msb(), lhs.source_location());

    if(from > to)
      std::swap(from, to);

    auto offset = mp_integer{src.type().get_int(ID_C_offset)};

    return lhst{
      to_symbol_expr(src), verilog_rtl_slicet{from - offset, to - offset}};
  }
  else if(
    lhs.id() == ID_verilog_indexed_part_select_plus ||
    lhs.id() == ID_verilog_indexed_part_select_minus)
  {
    auto &part_select = to_verilog_indexed_part_select_plus_or_minus_expr(lhs);
    auto &src = part_select.src();

    if(src.id() != ID_symbol)
    {
      throw errort().with_location(lhs.source_location())
        << "unsupported lvalue for RTL construction";
    }

    auto index = constant_value(part_select.index(), lhs.source_location());
    auto width = constant_value(part_select.width(), lhs.source_location());

    mp_integer lo, hi;

    if(lhs.id() == ID_verilog_indexed_part_select_plus)
    {
      lo = index;
      hi = index + width - 1;
    }
    else // ID_verilog_indexed_part_select_minus
    {
      lo = index - width + 1;
      hi = index;
    }

    auto offset = mp_integer{src.type().get_int(ID_C_offset)};

    return lhst{
      to_symbol_expr(src), verilog_rtl_slicet{lo - offset, hi - offset}};
  }
  else
  {
    throw errort().with_location(lhs.source_location())
      << "unsupported lvalue for RTL construction: `" << lhs.id() << "'";
  }
}

/*******************************************************************\

Function: verilog_rtl_buildert::slice_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_rtl_buildert::slice_of(
  const symbol_exprt &symbol,
  const verilog_rtl_slicet &slice)
{
  if(slice == whole_slice(symbol))
    return symbol;

  if(slice.width() == 1)
  {
    return extractbit_exprt{symbol, from_integer(slice.lower, integer_typet{})};
  }

  auto width = numeric_cast_v<std::size_t>(slice.width());

  return extractbits_exprt{
    symbol,
    from_integer(slice.lower, integer_typet{}),
    unsignedbv_typet{width}};
}

/*******************************************************************\

Function: verilog_rtl_buildert::substitute

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_rtl_buildert::substitute(exprt expr, const statet &state)
{
  if(expr.id() == ID_symbol)
  {
    auto &identifier = to_symbol_expr(expr).get_identifier();

    if(state.partial_blocking.find(identifier) != state.partial_blocking.end())
    {
      throw errort().with_location(expr.source_location())
        << "RTL construction does not support reading a variable "
           "after a blocking assignment to a part of it";
    }

    auto value_it = state.blocking_values.find(identifier);

    if(value_it != state.blocking_values.end())
      return typecast_exprt::conditional_cast(value_it->second, expr.type());

    return expr;
  }

  for(auto &op : expr.operands())
    op = substitute(op, state);

  return expr;
}

/*******************************************************************\

Function: verilog_rtl_buildert::extract_range

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_rtl_buildert::extract_range(
  const exprt &value,
  const verilog_rtl_slicet &from,
  const verilog_rtl_slicet &sub)
{
  PRECONDITION(from.lower <= sub.lower && sub.higher <= from.higher);

  if(sub == from)
    return value;

  if(sub.width() == 1)
  {
    return extractbit_exprt{
      value, from_integer(sub.lower - from.lower, integer_typet{})};
  }

  auto width = numeric_cast_v<std::size_t>(sub.width());

  return extractbits_exprt{
    value,
    from_integer(sub.lower - from.lower, integer_typet{}),
    unsignedbv_typet{width}};
}

/*******************************************************************\

Function: verilog_rtl_buildert::write_slice

  Inputs:

 Outputs:

 Purpose: Records the value of a slice. Any previously recorded
          overlapping slice is split so that the slices in the
          map remain pairwise disjoint.

\*******************************************************************/

void verilog_rtl_buildert::write_slice(
  statet::slice_valuest &slice_values,
  const verilog_rtl_slicet &slice,
  exprt value)
{
  for(auto it = slice_values.begin(); it != slice_values.end();)
  {
    if(it->first.overlaps(slice))
    {
      auto old_slice = it->first;
      auto old_value = it->second;
      it = slice_values.erase(it);

      // keep the part below the new slice, if any
      if(old_slice.lower < slice.lower)
      {
        verilog_rtl_slicet below{old_slice.lower, slice.lower - 1};
        slice_values.emplace(below, extract_range(old_value, old_slice, below));
      }

      // keep the part above the new slice, if any
      if(old_slice.higher > slice.higher)
      {
        verilog_rtl_slicet above{slice.higher + 1, old_slice.higher};
        slice_values.emplace(above, extract_range(old_value, old_slice, above));
      }
    }
    else
      ++it;
  }

  slice_values.emplace(slice, std::move(value));
}

/*******************************************************************\

Function: verilog_rtl_buildert::fragment_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_rtl_buildert::fragment_value(
  const statet::slice_valuest &slice_values,
  const verilog_rtl_slicet &fragment,
  const symbol_exprt &symbol)
{
  for(auto &entry : slice_values)
  {
    if(
      entry.first.lower <= fragment.lower &&
      fragment.higher <= entry.first.higher)
    {
      return extract_range(entry.second, entry.first, fragment);
    }
  }

  // not recorded: the fragment holds its current value
  return slice_of(symbol, fragment);
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::build_assign(
  const verilog_assignt &assign,
  statet &state,
  bool blocking)
{
  auto rhs = substitute(assign.rhs(), state);
  auto lhs = decompose_lhs(assign.lhs());

  write_slice(state.values[lhs.symbol.get_identifier()], lhs.slice, rhs);

  if(blocking)
  {
    if(lhs.slice == whole_slice(lhs.symbol))
      state.blocking_values[lhs.symbol.get_identifier()] = rhs;
    else
      state.partial_blocking.insert(lhs.symbol.get_identifier());
  }
}

/*******************************************************************\

Function: verilog_rtl_buildert::merge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::merge(
  const exprt &cond,
  const statet &then_state,
  const statet &else_state,
  statet &dest)
{
  // merge the assigned values
  std::set<irep_idt> identifiers;

  for(auto &entry : then_state.values)
    identifiers.insert(entry.first);

  for(auto &entry : else_state.values)
    identifiers.insert(entry.first);

  dest.values.clear();

  static const statet::slice_valuest empty_slice_values;

  for(auto &identifier : identifiers)
  {
    const symbolt &symbol = ns.lookup(identifier);
    const symbol_exprt symbol_expr{identifier, symbol.type};

    auto map_of = [&](const statet &state) -> const statet::slice_valuest &
    {
      auto it = state.values.find(identifier);
      return it == state.values.end() ? empty_slice_values : it->second;
    };

    const auto &then_map = map_of(then_state);
    const auto &else_map = map_of(else_state);

    // The slices assigned in the two branches may differ, and may
    // overlap. We split them into fragments at the slice boundaries
    // of both branches.
    std::set<mp_integer> cut_points;

    for(auto &entry : then_map)
    {
      cut_points.insert(entry.first.lower);
      cut_points.insert(entry.first.higher + 1);
    }

    for(auto &entry : else_map)
    {
      cut_points.insert(entry.first.lower);
      cut_points.insert(entry.first.higher + 1);
    }

    auto covered =
      [](const statet::slice_valuest &map, const verilog_rtl_slicet &fragment)
    {
      for(auto &entry : map)
        if(entry.first.overlaps(fragment))
          return true;
      return false;
    };

    auto &dest_map = dest.values[identifier];

    for(auto it = cut_points.begin(); it != cut_points.end();)
    {
      auto next = std::next(it);
      if(next == cut_points.end())
        break;

      verilog_rtl_slicet fragment{*it, *next - 1};
      it = next;

      // only fragments that are assigned in at least one branch
      if(!covered(then_map, fragment) && !covered(else_map, fragment))
        continue;

      auto then_value = fragment_value(then_map, fragment, symbol_expr);
      auto else_value = fragment_value(else_map, fragment, symbol_expr);

      exprt merged;

      if(then_value == else_value)
        merged = then_value;
      else
      {
        merged = if_exprt{
          cond,
          then_value,
          typecast_exprt::conditional_cast(else_value, then_value.type())};
      }

      write_slice(dest_map, fragment, std::move(merged));
    }
  }

  // merge the blocking-assignment values
  std::set<irep_idt> blocking_identifiers;

  for(auto &entry : then_state.blocking_values)
    blocking_identifiers.insert(entry.first);

  for(auto &entry : else_state.blocking_values)
    blocking_identifiers.insert(entry.first);

  dest.blocking_values.clear();

  for(auto &identifier : blocking_identifiers)
  {
    const symbolt &symbol = ns.lookup(identifier);
    const symbol_exprt symbol_expr{identifier, symbol.type};

    auto value_in = [&](const std::map<irep_idt, exprt> &map) -> exprt
    {
      auto it = map.find(identifier);
      return it == map.end() ? symbol_expr : it->second;
    };

    auto then_value = value_in(then_state.blocking_values);
    auto else_value = value_in(else_state.blocking_values);

    if(then_value == else_value)
      dest.blocking_values[identifier] = then_value;
    else
    {
      dest.blocking_values[identifier] = if_exprt{
        cond,
        typecast_exprt::conditional_cast(then_value, symbol.type),
        typecast_exprt::conditional_cast(else_value, symbol.type)};
    }
  }

  // merge the partial-blocking sets
  dest.partial_blocking.insert(
    then_state.partial_blocking.begin(), then_state.partial_blocking.end());
  dest.partial_blocking.insert(
    else_state.partial_blocking.begin(), else_state.partial_blocking.end());
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::build_if(
  const verilog_ift &if_statement,
  statet &state)
{
  auto cond = typecast_exprt::conditional_cast(
    substitute(if_statement.cond(), state), bool_typet{});

  statet then_state(state), else_state(state);

  build_statement(if_statement.then_case(), then_state);

  if(if_statement.has_else_case())
    build_statement(if_statement.else_case(), else_state);

  merge(cond, then_state, else_state, state);
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_statement

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::build_statement(
  const verilog_statementt &statement,
  statet &state)
{
  if(statement.id() == ID_block)
  {
    for(auto &block_statement : to_verilog_block(statement).statements())
      build_statement(block_statement, state);
  }
  else if(statement.id() == ID_verilog_blocking_assign)
  {
    build_assign(to_verilog_assign(statement), state, true);
  }
  else if(statement.id() == ID_verilog_non_blocking_assign)
  {
    build_assign(to_verilog_assign(statement), state, false);
  }
  else if(statement.id() == ID_if)
  {
    build_if(to_verilog_if(statement), state);
  }
  else if(statement.id() == ID_skip)
  {
    // ignore
  }
  else
  {
    throw errort().with_location(statement.source_location())
      << "statement `" << statement.id()
      << "' is not supported by RTL construction";
  }
}

/*******************************************************************\

Function: verilog_rtl_buildert::commit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::commit(
  const statet &state,
  kindt kind,
  const source_locationt &source_location)
{
  for(auto &value_entry : state.values)
  {
    auto &identifier = value_entry.first;
    auto &slice_map = rtl.identifier_map[identifier];

    for(auto &slice_entry : value_entry.second)
    {
      auto &slice = slice_entry.first;

      for(auto &existing : slice_map)
      {
        if(existing.first.overlaps(slice))
        {
          throw errort().with_location(source_location)
            << "`" << identifier << "' has multiple drivers";
        }
      }

      slice_map.emplace(
        slice, verilog_rtl_definitiont{kind, slice_entry.second});
    }
  }
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_always

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::build_always(const verilog_always_baset &always)
{
  const verilog_statementt *body = &always.statement();
  bool clocked = false;

  if(always.id() == ID_verilog_always_latch)
  {
    throw errort().with_location(always.source_location())
      << "always_latch is not supported by RTL construction";
  }

  if(body->id() == ID_event_guard)
  {
    auto &event_guard = to_verilog_event_guard(*body);
    auto &guard = event_guard.guard();

    // any edge in the guard makes this a clocked process
    if(guard.id() == ID_posedge || guard.id() == ID_negedge)
      clocked = true;
    else
    {
      for(auto &op : guard.operands())
        if(op.id() == ID_posedge || op.id() == ID_negedge)
          clocked = true;
    }

    body = &event_guard.body();
  }
  else if(always.id() == ID_verilog_always)
  {
    throw errort().with_location(always.source_location())
      << "expected event guard in always construct";
  }

  statet state;
  build_statement(*body, state);

  commit(
    state,
    clocked ? kindt::STATE_HOLDING : kindt::WIRE,
    always.source_location());
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_continuous_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::build_continuous_assign(
  const verilog_continuous_assignt &module_item)
{
  for(auto &assignment : module_item.operands())
  {
    auto &equal_expr = to_equal_expr(assignment);

    statet state;

    auto lhs = decompose_lhs(equal_expr.lhs());

    write_slice(
      state.values[lhs.symbol.get_identifier()], lhs.slice, equal_expr.rhs());

    commit(state, kindt::WIRE, module_item.source_location());
  }
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_module_item

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::build_module_item(
  const verilog_module_itemt &module_item)
{
  if(
    module_item.id() == ID_verilog_always ||
    module_item.id() == ID_verilog_always_comb ||
    module_item.id() == ID_verilog_always_ff ||
    module_item.id() == ID_verilog_always_latch)
  {
    build_always(to_verilog_always_base(module_item));
  }
  else if(module_item.id() == ID_continuous_assign)
  {
    build_continuous_assign(to_verilog_continuous_assign(module_item));
  }
  else
  {
    // Declarations, initial blocks, assertions, module instances
    // and other module items do not contribute to the RTL
    // representation.
  }
}

/*******************************************************************\

Function: verilog_rtl_buildert::build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

verilog_rtlt verilog_rtl_buildert::build()
{
  const symbolt &module_symbol = ns.lookup(module);

  // The module must be type checked, but not yet synthesized.
  if(module_symbol.value.id() != ID_verilog_module)
  {
    throw errort() << "module `" << module
                   << "' is not a type-checked Verilog module";
  }

  for(auto &module_item :
      to_verilog_module_expr(module_symbol.value).module_items())
  {
    build_module_item(module_item);
  }

  return std::move(rtl);
}

/*******************************************************************\

Function: verilog_rtlt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtlt::output(const namespacet &ns, std::ostream &out) const
{
  for(auto &identifier_entry : identifier_map)
  {
    for(auto &slice_entry : identifier_entry.second)
    {
      auto &slice = slice_entry.first;
      auto &definition = slice_entry.second;

      out << strip_verilog_prefix(identifier_entry.first) << '[' << slice.higher
          << ':' << slice.lower << "] ";

      if(definition.is_state_holding())
        out << "register, next-state value: ";
      else
        out << "wire, value: ";

      out << expr2verilog(definition.value, ns) << '\n';
    }
  }
}

/*******************************************************************\

Function: verilog_rtl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

verilog_rtlt verilog_rtl(
  const symbol_table_baset &symbol_table,
  const irep_idt &module_identifier,
  verilog_standardt standard,
  message_handlert &message_handler)
{
  const namespacet ns(symbol_table);

  verilog_rtl_buildert builder(
    standard, ns, module_identifier, message_handler);

  try
  {
    return builder.build();
  }
  catch(verilog_rtl_buildert::errort error)
  {
    messaget message{message_handler};

    if(error.what().empty())
      message.error();
    else
    {
      message.error().source_location = error.source_location();
      message.error() << error.what() << messaget::eom;
    }

    throw ebmc_errort{};
  }
}
