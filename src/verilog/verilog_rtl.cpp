/*******************************************************************\

Module: Verilog Register-Transfer Level Representation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_rtl.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/expr_util.h>
#include <util/mathematical_types.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/symbol_table_base.h>

#include <ebmc/ebmc_error.h>

#include "aval_bval_encoding.h"
#include "expr2verilog.h"
#include "sva_expr.h"
#include "verilog_bits.h"
#include "verilog_expr.h"
#include "verilog_typecheck_base.h"
#include "verilog_typecheck_expr.h"
#include "verilog_types.h"

#include <algorithm>
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
    const symbol_table_baset &_symbol_table,
    const namespacet &_ns,
    const irep_idt &_module,
    message_handlert &_message_handler)
    : verilog_typecheck_baset(_standard, _ns, _message_handler),
      module(_module),
      symbol_table(_symbol_table),
      message_handler(_message_handler)
  {
  }

  void typecheck() override
  {
  }

  // throws errort on error
  verilog_rtlt build();

protected:
  const irep_idt module;
  const symbol_table_baset &symbol_table;
  message_handlert &message_handler;
  verilog_rtlt rtl;

  /// the context in which properties are recorded
  verilog_rtl_propertyt::contextt property_context =
    verilog_rtl_propertyt::contextt::MODULE_LEVEL;

  /// the default disable iff condition, per module or generate block
  std::optional<exprt> default_disable_iff;

  using kindt = verilog_rtl_definitiont::kindt;

  /// the state while processing the statements of one always construct
  class statet
  {
  public:
    /// values assigned so far, per identifier and slice
    using slice_valuest = std::map<verilog_rtl_slicet, exprt>;
    using value_mapt = std::map<irep_idt, slice_valuest>;

    /// values assigned so far, by blocking and non-blocking assignments
    value_mapt values;

    /// values assigned by blocking assignments;
    /// these are substituted into subsequent right-hand sides
    value_mapt blocking_values;

    /// the path condition; 'false' is pushed by break, continue
    /// and return statements to mark the rest of the path dead
    exprt::operandst guard;
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
  void build_module(const symbolt &module_symbol);
  void build_module_item(const verilog_module_itemt &);
  void build_always(const verilog_always_baset &);
  void build_initial(const verilog_initialt &);
  void build_continuous_assign(const verilog_continuous_assignt &);
  void build_module_item_decl(const verilog_declt &);
  void build_property(const verilog_assert_assume_cover_module_itemt &);
  void build_instances(const verilog_instt &);
  void build_gate_instances(const verilog_inst_builtint &);

  // module instantiation
  void build_port_connections(
    const verilog_instt::instancet &,
    const symbolt &module_symbol);
  void build_port_connection(
    const module_typet::portt &,
    const exprt &value,
    const irep_idt &instance_identifier,
    const source_locationt &);
  void build_interface_port_connection(
    const module_typet::portt &,
    const exprt &value);

  /// per-loop state for break and continue statements
  class loop_framet
  {
  public:
    std::vector<statet> break_states, continue_states;
  };

  /// per-task/function state for return statements
  class tf_framet
  {
  public:
    std::vector<statet> return_states;
    std::optional<symbol_exprt> return_value;
  };

  /// The frames of the enclosing loop and of the enclosing task or
  /// function, if any. Passed down the statement recursion; break,
  /// continue and return statements record their state in the
  /// respective frame.
  class framest
  {
  public:
    loop_framet *loop = nullptr;
    tf_framet *tf = nullptr;
  };

  // statements
  void build_statement(const verilog_statementt &, statet &, const framest &);
  void build_assign(const verilog_assignt &, statet &, bool blocking);
  void build_compound_assign(const verilog_assignt &, statet &, irep_idt op_id);
  void
  build_case(const verilog_case_statement_baset &, statet &, const framest &);
  void build_for(const verilog_fort &, statet &, const framest &);
  void build_function_call(
    const verilog_function_callt &,
    statet &,
    const framest &);
  void build_if(const verilog_ift &, statet &, const framest &);
  void build_incdec(const verilog_statementt &, statet &);

  /// record an assert, assume or cover statement as a property;
  /// the optional label stems from an enclosing labeled statement
  void build_check(
    const verilog_assert_assume_cover_statementt &,
    const irep_idt &label,
    statet &);

  /// assign the given (already substituted) rhs to the given lvalue
  void assign_to(const exprt &lhs, exprt rhs, statet &, bool blocking);

  /// record the assignment of the given value to the given slice
  /// of the given symbol, maintaining the invariants of the state
  void record_assignment(
    const symbol_exprt &,
    const verilog_rtl_slicet &,
    exprt value,
    statet &,
    bool blocking);

  /// prefixes of identifiers that are local to a function or task;
  /// these are not part of the RTL representation
  std::set<std::string> cycle_local_prefixes;

  bool is_cycle_local(const irep_idt &identifier) const
  {
    for(auto &prefix : cycle_local_prefixes)
      if(identifier.starts_with(prefix))
        return true;
    return false;
  }

  /// the property kind of the given assert, assume or cover
  /// statement or module item, or {} for other ids
  static std::optional<verilog_rtl_propertyt::kindt>
  property_kind(const irep_idt &id)
  {
    using kindt = verilog_rtl_propertyt::kindt;

    if(
      id == ID_verilog_immediate_assert || id == ID_verilog_assert_property ||
      id == ID_verilog_smv_assert)
    {
      return kindt::ASSERT;
    }
    else if(
      id == ID_verilog_immediate_assume || id == ID_verilog_assume_property ||
      id == ID_verilog_restrict_property || id == ID_verilog_smv_assume)
    {
      return kindt::ASSUME;
    }
    else if(
      id == ID_verilog_immediate_cover || id == ID_verilog_cover_property ||
      id == ID_verilog_cover_sequence)
    {
      return kindt::COVER;
    }
    else
      return {};
  }

  /// Record that the given lvalue is forced to a value,
  /// e.g. by a port connection; forced variables become wires.
  /// Identifiers inside the given instance are not affected, since
  /// the instance has already been processed.
  void record_forced(const exprt &lhs, const irep_idt &instance_identifier)
  {
    if(lhs.id() == ID_symbol)
    {
      auto &identifier = to_symbol_expr(lhs).get_identifier();
      if(!identifier.starts_with(id2string(instance_identifier) + '.'))
        rtl.forced.insert(identifier);
    }
    else if(lhs.id() == ID_concatenation)
    {
      for(auto &op : lhs.operands())
        record_forced(op, instance_identifier);
    }
    else if(lhs.id() == ID_typecast)
      record_forced(to_typecast_expr(lhs).op(), instance_identifier);
    else if(
      lhs.id() == ID_verilog_bit_select ||
      lhs.id() == ID_verilog_non_indexed_part_select ||
      lhs.id() == ID_verilog_indexed_part_select_plus ||
      lhs.id() == ID_verilog_indexed_part_select_minus || lhs.id() == ID_member)
    {
      record_forced(to_multi_ary_expr(lhs).op0(), instance_identifier);
    }
    else if(lhs.id() == ID_hierarchical_identifier)
    {
      record_forced(
        resolve_hierarchical_identifier(to_hierarchical_identifier_expr(lhs)),
        instance_identifier);
    }
  }

  /// record a declared variable; unassigned variables hold
  /// their value
  void record_variable(const irep_idt &identifier)
  {
    if(is_cycle_local(identifier))
      return;

    const symbolt *symbol;
    if(ns.lookup(identifier, symbol))
      return;

    if(
      symbol->is_lvalue && !symbol->is_macro && symbol->type.id() != ID_integer)
    {
      rtl.variables.insert(identifier);
    }
  }

  /// is the given statement an assertion or a similar check?
  static bool is_check(const irep_idt &id)
  {
    return property_kind(id).has_value();
  }

  /// does the given statement consist of checks only,
  /// i.e., is free of side effects on the state?
  static bool is_check_only(const verilog_statementt &);

  /// the bits of a constant pattern as a string of
  /// '0', '1', 'x', 'z', '?' characters, most significant first,
  /// or {} if the pattern is not constant
  static std::optional<std::string> pattern_bits(const exprt &);

  /// the constant value of a supply0 or supply1 net
  exprt supply_value(const irep_idt &decl_class, const typet &);

  /// is the given pattern bit a wildcard, given the kind of
  /// case statement?
  static bool is_wildcard_bit(const irep_idt &case_type, char bit);

  /// the condition under which the case operand matches the
  /// given pattern
  exprt case_comparison(
    const irep_idt &case_type,
    const exprt &case_operand,
    const exprt &pattern);

  /// the condition under which the case operand matches one of the
  /// patterns of a case item
  exprt case_values(
    const irep_idt &case_type,
    const exprt &values,
    const exprt &case_operand,
    statet &);

  void merge(
    const exprt &cond,
    const statet &then_state,
    const statet &else_state,
    statet &dest);

  /// the slice values recorded for the given identifier,
  /// or an empty map if none are recorded
  static const statet::slice_valuest &
  slice_values_of(const statet::value_mapt &, const irep_idt &);

  /// is any part of the given fragment assigned in the given map?
  static bool covers(const statet::slice_valuest &, const verilog_rtl_slicet &);

  /// merge the values assigned in the two branches
  void merge_maps(
    const exprt &cond,
    const statet::value_mapt &then_map,
    const statet::value_mapt &else_map,
    statet::value_mapt &dest_map);

  /// merge the slice values assigned to one identifier
  /// in the two branches
  void merge_slices(
    const exprt &cond,
    const statet::slice_valuest &then_map,
    const statet::slice_valuest &else_map,
    const symbol_exprt &,
    statet::slice_valuest &dest_map);

  /// Decompose an lvalue into its base symbol and the slice selected.
  /// Returns {} if the lvalue does not correspond to a constant slice.
  std::optional<lhst> decompose_lhs(const exprt &lhs, statet &);

  /// an lvalue lowered to an assignment of a whole symbol
  class loweredt
  {
  public:
    symbol_exprt symbol;
    exprt value;

    loweredt(symbol_exprt _symbol, exprt _value)
      : symbol(std::move(_symbol)), value(std::move(_value))
    {
    }
  };

  /// Rewrite the assignment lhs = rhs into an equivalent assignment
  /// to a whole symbol, using with-expressions. Used for lvalues that
  /// do not correspond to a constant slice, e.g., array elements with
  /// a non-constant index.
  loweredt lower_lhs(const exprt &lhs, exprt rhs, statet &);

  /// the current value of the given lvalue-shaped expression,
  /// composing the values recorded in the given state
  exprt read_lhs(exprt, statet &);

  /// the LSB offset and the width of the given member
  /// of a struct or union type
  std::pair<mp_integer, mp_integer> member_slice(
    const typet &compound,
    const irep_idt &component_name,
    const source_locationt &);

  /// evaluate the given expression to a constant, using the
  /// blocking-assignment values in the given state
  std::optional<mp_integer> constant_index(const exprt &, statet &);

  /// constant-fold system function calls such as $bits
  exprt fold_system_functions(exprt) const;

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

  /// apply the blocking-assignment values to the given rvalue,
  /// and expand function calls
  exprt substitute(exprt, statet &);

  /// inline a function call in an rvalue
  exprt expand_function_call(const function_call_exprt &, statet &);

  /// resolve a hierarchical identifier to a symbol
  exprt resolve_hierarchical_identifier(const hierarchical_identifier_exprt &);

  /// the value of the given symbol composed from the given
  /// slice values
  exprt composed_value(const statet::slice_valuest &, const symbol_exprt &);

  void commit(const statet &, kindt, const source_locationt &);

  /// The width of the entire identifier as a slice. Types without
  /// a fixed number of bits, e.g. chandles, are treated as a single
  /// slice; they are always assigned as a whole.
  verilog_rtl_slicet whole_slice(const symbol_exprt &symbol)
  {
    auto bits_opt = verilog_bits_opt(symbol.type());
    if(bits_opt.has_value())
      return verilog_rtl_slicet{0, *bits_opt - 1};
    else
      return verilog_rtl_slicet{0, 0};
  }
};

/*******************************************************************\

Function: verilog_rtl_buildert::fold_system_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_rtl_buildert::fold_system_functions(exprt expr) const
{
  for(auto &op : expr.operands())
    op = fold_system_functions(std::move(op));

  if(expr.id() == ID_function_call)
  {
    auto &call = to_function_call_expr(expr);

    if(call.is_system_function_call())
    {
      verilog_typecheck_exprt verilog_typecheck_expr(
        standard, false, ns, message_handler);

      try
      {
        auto result =
          verilog_typecheck_expr.elaborate_constant_system_function_call(call);
        if(result.is_constant())
          return result;
      }
      catch(verilog_typecheck_exprt::errort &)
      {
        // not constant; leave as is
      }
    }
  }

  return expr;
}

/*******************************************************************\

Function: verilog_rtl_buildert::constant_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::optional<mp_integer>
verilog_rtl_buildert::constant_index(const exprt &expr, statet &state)
{
  auto substituted = substitute(expr, state);
  auto folded = fold_system_functions(std::move(substituted));
  auto simplified = simplify_expr(std::move(folded), ns);
  return numeric_cast<mp_integer>(simplified);
}

/*******************************************************************\

Function: verilog_rtl_buildert::member_slice

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::pair<mp_integer, mp_integer> verilog_rtl_buildert::member_slice(
  const typet &compound,
  const irep_idt &component_name,
  const source_locationt &source_location)
{
  if(compound.id() == ID_struct)
  {
    // the first component is the most significant
    mp_integer offset = get_width(compound);

    for(auto &component : to_struct_type(compound).components())
    {
      auto width = get_width(component.type());
      offset -= width;
      if(component.get_name() == component_name)
        return {offset, width};
    }
  }
  else if(compound.id() == ID_union)
  {
    // all members of a packed union start at offset 0
    for(auto &component : to_verilog_union_type(compound).components())
    {
      if(component.get_name() == component_name)
        return {0, get_width(component.type())};
    }
  }
  else
  {
    throw errort().with_location(source_location)
      << "member select on unexpected type `" << compound.id() << "'";
  }

  throw errort().with_location(source_location)
    << "member `" << component_name << "' not found";
}

/*******************************************************************\

Function: verilog_rtl_buildert::decompose_lhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::optional<verilog_rtl_buildert::lhst>
verilog_rtl_buildert::decompose_lhs(const exprt &lhs, statet &state)
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

    auto index_opt = constant_index(bit_select.index(), state);

    if(!index_opt.has_value())
      return {};

    auto sub_opt = decompose_lhs(src, state);

    if(!sub_opt.has_value())
      return {};

    if(src.type().id() == ID_array)
    {
      // a bit select on an array selects an element
      auto &array_type = to_verilog_array_type(src.type());
      auto element_width = get_width(array_type.element_type());
      auto size = array_type.size_int();
      auto offset = array_type.offset();

      // elements are stored starting from the left index of the range
      auto internal = array_type.increasing()
                        ? *index_opt - offset
                        : (offset + size - 1) - *index_opt;

      if(internal < 0 || internal >= size)
      {
        throw errort().with_location(lhs.source_location())
          << "array index out of range";
      }

      auto lower = sub_opt->slice.lower + internal * element_width;

      return lhst{
        sub_opt->symbol, verilog_rtl_slicet{lower, lower + element_width - 1}};
    }
    else
    {
      auto offset = mp_integer{src.type().get_int(ID_C_offset)};
      auto bit = sub_opt->slice.lower + *index_opt - offset;

      return lhst{sub_opt->symbol, verilog_rtl_slicet{bit, bit}};
    }
  }
  else if(lhs.id() == ID_verilog_non_indexed_part_select)
  {
    auto &part_select = to_verilog_non_indexed_part_select_expr(lhs);
    auto &src = part_select.src();

    auto from_opt = constant_index(part_select.lsb(), state);
    auto to_opt = constant_index(part_select.msb(), state);

    if(!from_opt.has_value() || !to_opt.has_value())
      return {};

    auto sub_opt = decompose_lhs(src, state);

    if(!sub_opt.has_value())
      return {};

    auto from = *from_opt, to = *to_opt;

    if(from > to)
      std::swap(from, to);

    auto offset = mp_integer{src.type().get_int(ID_C_offset)};
    auto lower = sub_opt->slice.lower;

    return lhst{
      sub_opt->symbol,
      verilog_rtl_slicet{lower + from - offset, lower + to - offset}};
  }
  else if(
    lhs.id() == ID_verilog_indexed_part_select_plus ||
    lhs.id() == ID_verilog_indexed_part_select_minus)
  {
    auto &part_select = to_verilog_indexed_part_select_plus_or_minus_expr(lhs);
    auto &src = part_select.src();

    auto index_opt = constant_index(part_select.index(), state);
    auto width_opt = constant_index(part_select.width(), state);

    if(!index_opt.has_value() || !width_opt.has_value())
      return {};

    auto sub_opt = decompose_lhs(src, state);

    if(!sub_opt.has_value())
      return {};

    mp_integer lo, hi;

    if(lhs.id() == ID_verilog_indexed_part_select_plus)
    {
      lo = *index_opt;
      hi = *index_opt + *width_opt - 1;
    }
    else // ID_verilog_indexed_part_select_minus
    {
      lo = *index_opt - *width_opt + 1;
      hi = *index_opt;
    }

    auto offset = mp_integer{src.type().get_int(ID_C_offset)};
    auto lower = sub_opt->slice.lower;

    return lhst{
      sub_opt->symbol,
      verilog_rtl_slicet{lower + lo - offset, lower + hi - offset}};
  }
  else if(lhs.id() == ID_member)
  {
    auto &member_expr = to_member_expr(lhs);
    auto &compound = member_expr.struct_op();

    // Aggregate-typed members are assigned via with-expressions,
    // since their values cannot be reinterpreted by a typecast.
    if(
      lhs.type().id() == ID_array || lhs.type().id() == ID_struct ||
      lhs.type().id() == ID_union)
    {
      return {};
    }

    auto sub_opt = decompose_lhs(compound, state);

    if(!sub_opt.has_value())
      return {};

    auto offset_width = member_slice(
      compound.type(), member_expr.get_component_name(), lhs.source_location());

    auto lower = sub_opt->slice.lower + offset_width.first;

    return lhst{
      sub_opt->symbol,
      verilog_rtl_slicet{lower, lower + offset_width.second - 1}};
  }
  else if(lhs.id() == ID_typecast)
  {
    // assumed to be a reinterpret cast; the bit positions are unchanged
    return decompose_lhs(to_typecast_expr(lhs).op(), state);
  }
  else if(lhs.id() == ID_hierarchical_identifier)
  {
    return decompose_lhs(
      resolve_hierarchical_identifier(to_hierarchical_identifier_expr(lhs)),
      state);
  }
  else
    return {};
}

/*******************************************************************\

Function: verilog_rtl_buildert::read_lhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_rtl_buildert::read_lhs(exprt expr, statet &state)
{
  if(expr.id() == ID_symbol)
  {
    auto &symbol_expr = to_symbol_expr(expr);

    return fragment_value(
      slice_values_of(state.values, symbol_expr.get_identifier()),
      whole_slice(symbol_expr),
      symbol_expr);
  }

  // an lvalue-shaped expression: the first operand is the base
  auto &operands = expr.operands();

  PRECONDITION(!operands.empty());

  operands.front() = read_lhs(operands.front(), state);

  for(std::size_t i = 1; i < operands.size(); i++)
    operands[i] = substitute(operands[i], state);

  return expr;
}

/*******************************************************************\

Function: verilog_rtl_buildert::lower_lhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

verilog_rtl_buildert::loweredt
verilog_rtl_buildert::lower_lhs(const exprt &lhs, exprt rhs, statet &state)
{
  if(lhs.id() == ID_symbol)
  {
    return loweredt{to_symbol_expr(lhs), std::move(rhs)};
  }
  else if(lhs.id() == ID_verilog_bit_select)
  {
    // an array element or a bit of a vector; turn
    //   a[i]=e
    // into
    //   a = a WITH [i:=e]
    auto &bit_select = to_verilog_bit_select_expr(lhs);
    auto &src = bit_select.src();

    auto old_value = read_lhs(src, state);
    auto index = substitute(bit_select.index(), state);

    with_exprt new_value{
      std::move(old_value), std::move(index), std::move(rhs)};

    return lower_lhs(src, std::move(new_value), state); // recursive call
  }
  else if(lhs.id() == ID_member)
  {
    // turn
    //   s.m=e
    // into
    //   s = s WITH [m:=e]
    auto &member_expr = to_member_expr(lhs);
    auto &compound = member_expr.struct_op();

    auto old_value = read_lhs(compound, state);

    with_exprt new_value{
      std::move(old_value),
      member_designatort{member_expr.get_component_name()},
      std::move(rhs)};

    return lower_lhs(compound, std::move(new_value), state); // recursive call
  }
  else if(lhs.id() == ID_typecast)
  {
    // assumed to be a reinterpret cast
    auto &typecast_expr = to_typecast_expr(lhs);

    auto new_value =
      typecast_exprt::conditional_cast(rhs, typecast_expr.op().type());

    return lower_lhs(
      typecast_expr.op(), std::move(new_value), state); // recursive call
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

exprt verilog_rtl_buildert::substitute(exprt expr, statet &state)
{
  if(expr.id() == ID_symbol)
  {
    auto &symbol_expr = to_symbol_expr(expr);

    // Elaboration-time constants, e.g. parameters, are substituted.
    const symbolt *symbol;
    if(!ns.lookup(symbol_expr.get_identifier(), symbol))
    {
      if(symbol->is_macro && symbol->value.is_not_nil())
      {
        return typecast_exprt::conditional_cast(
          substitute(symbol->value, state), expr.type());
      }
    }

    auto value_it = state.blocking_values.find(symbol_expr.get_identifier());

    if(value_it != state.blocking_values.end())
    {
      auto composed = composed_value(value_it->second, symbol_expr);

      // Preserve the declared type of the symbol, including its
      // attributes (e.g. the range direction), which are stored
      // in comments and hence invisible to type comparison.
      if(!composed.type().full_eq(symbol_expr.type()))
        composed = typecast_exprt{std::move(composed), symbol_expr.type()};

      return composed;
    }

    return expr;
  }
  else if(expr.id() == ID_hierarchical_identifier)
  {
    return substitute(
      resolve_hierarchical_identifier(to_hierarchical_identifier_expr(expr)),
      state);
  }
  else if(expr.id() == ID_sva_sequence_property_instance)
  {
    // an instance of a named property or sequence
    auto &instance = to_sva_sequence_property_instance_expr(expr);
    return substitute(instance.declaration().cond(), state);
  }
  else if(expr.id() == ID_function_call)
  {
    auto &call = to_function_call_expr(expr);

    // User-defined functions are inlined; system functions
    // remain in the representation.
    if(!call.is_system_function_call())
      return expand_function_call(call, state);

    // Attempt to fold constant system functions before substitution,
    // since functions such as $left depend on the argument type.
    // Only functions that depend on the argument type alone
    // may be folded here.
    auto base_name = to_verilog_identifier_expr(call.function()).base_name();

    if(
      base_name == "$bits" || base_name == "$left" || base_name == "$right" ||
      base_name == "$low" || base_name == "$high" || base_name == "$size" ||
      base_name == "$increment" || base_name == "$typename")
    {
      verilog_typecheck_exprt verilog_typecheck_expr(
        standard, false, ns, message_handler);

      try
      {
        auto result =
          verilog_typecheck_expr.elaborate_constant_system_function_call(call);
        if(result.is_constant())
          return result;
      }
      catch(verilog_typecheck_exprt::errort &)
      {
        // not constant; leave as is
      }
    }
  }

  for(auto &op : expr.operands())
    op = substitute(op, state);

  return expr;
}

/*******************************************************************\

Function: verilog_rtl_buildert::resolve_hierarchical_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_rtl_buildert::resolve_hierarchical_identifier(
  const hierarchical_identifier_exprt &expr)
{
  exprt lhs = expr.lhs();

  if(lhs.id() == ID_hierarchical_identifier)
    lhs = resolve_hierarchical_identifier(to_hierarchical_identifier_expr(lhs));

  if(lhs.id() != ID_symbol)
  {
    throw errort().with_location(expr.source_location())
      << "expected symbol on lhs of `.'";
  }

  if(lhs.type().id() != ID_verilog_module_instance)
  {
    throw errort().with_location(expr.source_location())
      << "expected module instance on lhs of `.'";
  }

  auto &lhs_identifier = to_symbol_expr(lhs).get_identifier();
  auto &rhs_base_name = expr.rhs().base_name();

  // just patch together
  irep_idt full_identifier =
    id2string(lhs_identifier) + '.' + id2string(rhs_base_name);

  const symbolt *symbol;
  if(ns.lookup(full_identifier, symbol))
  {
    throw errort().with_location(expr.source_location())
      << "failed to find identifier `" << full_identifier << "'";
  }

  return symbol_exprt{full_identifier, symbol->type};
}

/*******************************************************************\

Function: verilog_rtl_buildert::expand_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_rtl_buildert::expand_function_call(
  const function_call_exprt &call,
  statet &state)
{
  auto &function = to_symbol_expr(call.function());
  const symbolt &symbol = ns.lookup(function.get_identifier());

  if(symbol.type.id() != ID_code)
  {
    throw errort().with_location(call.source_location())
      << "function call expects function argument";
  }

  auto &code_type = to_code_type(symbol.type);

  if(code_type.return_type() == empty_typet{})
  {
    throw errort().with_location(call.source_location())
      << "function call cannot call task";
  }

  // the local symbols of the function are not part
  // of the RTL representation
  cycle_local_prefixes.insert(id2string(symbol.name) + '.');

  auto &parameters = code_type.parameters();
  auto &actuals = call.arguments();

  if(parameters.size() != actuals.size())
  {
    throw errort().with_location(call.source_location())
      << "wrong number of arguments";
  }

  // The return value is assigned to the symbol
  // with the function's name.
  const symbolt &return_symbol =
    ns.lookup(id2string(symbol.name) + "." + id2string(symbol.base_name));

  tf_framet tf_frame;
  tf_frame.return_value = return_symbol.symbol_expr();
  framest body_frames{nullptr, &tf_frame};

  // remember the guard
  auto entry_guard = state.guard;

  // do assignments to input parameters
  for(std::size_t i = 0; i < parameters.size(); i++)
  {
    if(parameters[i].get_bool(ID_input))
    {
      const symbolt &parameter_symbol =
        ns.lookup(parameters[i].get_identifier());
      assign_to(
        parameter_symbol.symbol_expr(),
        substitute(actuals[i], state),
        state,
        true);
    }
  }

  // the body
  for(auto &body_statement : symbol.value.operands())
    build_statement(to_verilog_statement(body_statement), state, body_frames);

  // merge in edges from 'return' statements, if any
  for(auto &return_state : tf_frame.return_states)
  {
    statet current(state);
    merge(conjunction(return_state.guard), return_state, current, state);
  }

  // restore the guard
  state.guard = std::move(entry_guard);

  // do assignments to output parameters
  for(std::size_t i = 0; i < parameters.size(); i++)
  {
    if(parameters[i].get_bool(ID_output))
    {
      const symbolt &parameter_symbol =
        ns.lookup(parameters[i].get_identifier());
      assign_to(
        actuals[i],
        substitute(parameter_symbol.symbol_expr(), state),
        state,
        true);
    }
  }

  // the result is the value of the return symbol
  return typecast_exprt::conditional_cast(
    substitute(return_symbol.symbol_expr(), state), call.type());
}

/*******************************************************************\

Function: verilog_rtl_buildert::composed_value

  Inputs:

 Outputs:

 Purpose: Composes the value of the given symbol from the given
          slice values. Slices that are not recorded hold the
          current value of the symbol.

\*******************************************************************/

exprt verilog_rtl_buildert::composed_value(
  const statet::slice_valuest &slice_values,
  const symbol_exprt &symbol)
{
  auto whole = whole_slice(symbol);

  // the fragment boundaries
  std::set<mp_integer> cut_points;

  cut_points.insert(whole.lower);
  cut_points.insert(whole.higher + 1);

  for(auto &entry : slice_values)
  {
    cut_points.insert(entry.first.lower);
    cut_points.insert(entry.first.higher + 1);
  }

  // the fragment values, from least to most significant
  exprt::operandst fragments;

  for(auto it = cut_points.begin(); it != cut_points.end();)
  {
    auto next = std::next(it);
    if(next == cut_points.end())
      break;

    verilog_rtl_slicet fragment{*it, *next - 1};
    it = next;

    fragments.push_back(fragment_value(slice_values, fragment, symbol));
  }

  DATA_INVARIANT(!fragments.empty(), "symbol must have at least one fragment");

  if(fragments.size() == 1)
    return typecast_exprt::conditional_cast(fragments.front(), symbol.type());

  // concatenations take the most significant operand first
  std::reverse(fragments.begin(), fragments.end());

  auto width = numeric_cast_v<std::size_t>(whole.width());

  return typecast_exprt::conditional_cast(
    concatenation_exprt{std::move(fragments), unsignedbv_typet{width}},
    symbol.type());
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

  // Can the rhs be simplified to a constant, for propagation?
  auto rhs_simplified = simplify_expr(fold_system_functions(rhs), ns);

  if(rhs_simplified.is_constant())
    rhs = rhs_simplified;

  assign_to(assign.lhs(), std::move(rhs), state, blocking);
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_compound_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::build_compound_assign(
  const verilog_assignt &assign,
  statet &state,
  irep_idt op_id)
{
  // turn lhs op= rhs into lhs = lhs op rhs
  auto rhs = substitute(
    binary_exprt{assign.lhs(), op_id, assign.rhs(), assign.rhs().type()},
    state);

  // Can the rhs be simplified to a constant, for propagation?
  auto rhs_simplified = simplify_expr(fold_system_functions(rhs), ns);

  if(rhs_simplified.is_constant())
    rhs = rhs_simplified;

  assign_to(assign.lhs(), std::move(rhs), state, true);
}

/*******************************************************************\

Function: verilog_rtl_buildert::assign_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::assign_to(
  const exprt &lhs,
  exprt rhs,
  statet &state,
  bool blocking)
{
  // Assignments to reals are silently ignored.
  if(lhs.type().id() == ID_verilog_realtime)
    return;

  if(lhs.id() == ID_concatenation)
  {
    // split it up, from right to left
    mp_integer offset = 0;

    for(auto it = lhs.operands().rbegin(); it != lhs.operands().rend(); it++)
    {
      auto offset_constant = from_integer(offset, integer_typet{});
      auto width = get_width(it->type());

      exprt part;

      if(width == 1 && it->type().id() == ID_bool)
        part = extractbit_exprt{rhs, std::move(offset_constant)};
      else
      {
        part = extractbits_exprt{
          rhs,
          std::move(offset_constant),
          unsignedbv_typet{numeric_cast_v<std::size_t>(width)}};
      }

      assign_to(*it, std::move(part), state, blocking); // recursive call

      offset += width;
    }

    return;
  }

  if(auto lhs_opt = decompose_lhs(lhs, state))
  {
    auto whole = whole_slice(lhs_opt->symbol);
    auto slice = lhs_opt->slice;

    // Bits outside of the symbol are ignored (1800-2017 11.5.1).
    if(slice.lower < whole.lower || slice.higher > whole.higher)
    {
      auto clipped_lower = std::max(slice.lower, whole.lower);
      auto clipped_higher = std::min(slice.higher, whole.higher);

      if(clipped_lower > clipped_higher)
        return; // nothing to assign

      verilog_rtl_slicet clipped{clipped_lower, clipped_higher};
      rhs = extract_range(rhs, slice, clipped);
      slice = clipped;
    }

    record_assignment(lhs_opt->symbol, slice, std::move(rhs), state, blocking);
  }
  else
  {
    // Not a constant slice, e.g., an array element with a
    // non-constant index. Rewrite into an assignment to the
    // whole symbol.
    auto lowered = lower_lhs(lhs, std::move(rhs), state);
    record_assignment(
      lowered.symbol,
      whole_slice(lowered.symbol),
      std::move(lowered.value),
      state,
      blocking);
  }
}

/*******************************************************************\

Function: verilog_rtl_buildert::record_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::record_assignment(
  const symbol_exprt &symbol,
  const verilog_rtl_slicet &slice,
  exprt value,
  statet &state,
  bool blocking)
{
  write_slice(state.values[symbol.get_identifier()], slice, value);

  if(blocking)
  {
    write_slice(
      state.blocking_values[symbol.get_identifier()], slice, std::move(value));
  }
}

/*******************************************************************\

Function: verilog_rtl_buildert::slice_values_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const verilog_rtl_buildert::statet::slice_valuest &
verilog_rtl_buildert::slice_values_of(
  const statet::value_mapt &value_map,
  const irep_idt &identifier)
{
  static const statet::slice_valuest empty_slice_values;

  auto it = value_map.find(identifier);
  return it == value_map.end() ? empty_slice_values : it->second;
}

/*******************************************************************\

Function: verilog_rtl_buildert::covers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_rtl_buildert::covers(
  const statet::slice_valuest &slice_values,
  const verilog_rtl_slicet &fragment)
{
  for(auto &entry : slice_values)
    if(entry.first.overlaps(fragment))
      return true;

  return false;
}

/*******************************************************************\

Function: verilog_rtl_buildert::merge_slices

  Inputs:

 Outputs:

 Purpose: Merges the slice values assigned to one identifier in the
          two branches. The slices assigned in the two branches may
          differ, and may overlap. They are split into fragments at
          the slice boundaries of both branches.

\*******************************************************************/

void verilog_rtl_buildert::merge_slices(
  const exprt &cond,
  const statet::slice_valuest &then_map,
  const statet::slice_valuest &else_map,
  const symbol_exprt &symbol_expr,
  statet::slice_valuest &dest_map)
{
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

  for(auto it = cut_points.begin(); it != cut_points.end();)
  {
    auto next = std::next(it);
    if(next == cut_points.end())
      break;

    verilog_rtl_slicet fragment{*it, *next - 1};
    it = next;

    // only fragments that are assigned in at least one branch
    if(!covers(then_map, fragment) && !covers(else_map, fragment))
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

/*******************************************************************\

Function: verilog_rtl_buildert::merge_maps

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::merge_maps(
  const exprt &cond,
  const statet::value_mapt &then_map,
  const statet::value_mapt &else_map,
  statet::value_mapt &dest_map)
{
  std::set<irep_idt> identifiers;

  for(auto &entry : then_map)
    identifiers.insert(entry.first);

  for(auto &entry : else_map)
    identifiers.insert(entry.first);

  dest_map.clear();

  for(auto &identifier : identifiers)
  {
    const symbolt &symbol = ns.lookup(identifier);
    const symbol_exprt symbol_expr{identifier, symbol.type};

    merge_slices(
      cond,
      slice_values_of(then_map, identifier),
      slice_values_of(else_map, identifier),
      symbol_expr,
      dest_map[identifier]);
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
  merge_maps(cond, then_state.values, else_state.values, dest.values);

  merge_maps(
    cond,
    then_state.blocking_values,
    else_state.blocking_values,
    dest.blocking_values);
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::build_if(
  const verilog_ift &if_statement,
  statet &state,
  const framest &frames)
{
  auto cond = typecast_exprt::conditional_cast(
    substitute(if_statement.cond(), state), bool_typet{});

  // Constant conditions do not branch; this keeps the path
  // condition of break, continue and return statements alive.
  auto cond_simplified = simplify_expr(fold_system_functions(cond), ns);

  if(cond_simplified.is_true())
  {
    build_statement(if_statement.then_case(), state, frames);
    return;
  }
  else if(cond_simplified.is_false())
  {
    if(if_statement.has_else_case())
      build_statement(if_statement.else_case(), state, frames);
    return;
  }

  statet then_state(state), else_state(state);

  then_state.guard.push_back(cond);
  else_state.guard.push_back(not_exprt{cond});

  build_statement(if_statement.then_case(), then_state, frames);

  if(if_statement.has_else_case())
    build_statement(if_statement.else_case(), else_state, frames);

  merge(cond, then_state, else_state, state);
}

/*******************************************************************\

Function: verilog_rtl_buildert::is_check_only

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_rtl_buildert::is_check_only(const verilog_statementt &statement)
{
  if(statement.id() == ID_skip || is_check(statement.id()))
    return true;
  else if(statement.id() == ID_block)
  {
    for(auto &block_statement : to_verilog_block(statement).statements())
      if(!is_check_only(block_statement))
        return false;
    return true;
  }
  else if(statement.id() == ID_verilog_label_statement)
  {
    return is_check_only(to_verilog_label_statement(statement).statement());
  }
  else
    return false;
}

/*******************************************************************\

Function: verilog_rtl_buildert::case_comparison

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

/*******************************************************************\

Function: verilog_rtl_buildert::pattern_bits

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::optional<std::string>
verilog_rtl_buildert::pattern_bits(const exprt &pattern)
{
  auto width_opt = verilog_bits_opt(pattern.type());

  if(!width_opt.has_value())
    return {};

  auto width = numeric_cast_v<std::size_t>(*width_opt);

  if(pattern.is_constant())
  {
    if(is_four_valued(pattern.type()))
    {
      auto &value = id2string(to_constant_expr(pattern).get_value());

      // pad from the left with '0'
      std::string result(width, '0');

      for(std::size_t bit = 0; bit < width && bit < value.size(); bit++)
        result[width - 1 - bit] = value[value.size() - 1 - bit];

      return result;
    }
    else
    {
      auto value_opt = numeric_cast<mp_integer>(pattern);
      if(!value_opt.has_value())
        return {};

      std::string result(width, '0');

      for(std::size_t bit = 0; bit < width; bit++)
        if(((*value_opt >> bit) % 2) != 0)
          result[width - 1 - bit] = '1';

      return result;
    }
  }
  else if(pattern.id() == ID_concatenation)
  {
    // most significant operand first
    std::string result;

    for(auto &op : pattern.operands())
    {
      auto op_bits = pattern_bits(op);
      if(!op_bits.has_value())
        return {};
      result += *op_bits;
    }

    // Concatenations are unsigned (1800-2017 11.8.1); the type of the
    // pattern may be wider, e.g. owing to the type of the case
    // expression, in which case the value is zero-extended.
    if(result.size() < width)
      result.insert(0, width - result.size(), '0');
    else if(result.size() > width)
      result.erase(0, result.size() - width);

    return result;
  }
  else if(pattern.id() == ID_typecast)
  {
    // The type checker gives all case expressions the max type
    // (1800-2017 12.5), which may widen the pattern.
    auto &op = to_typecast_expr(pattern).op();
    auto op_bits = pattern_bits(op);

    if(!op_bits.has_value())
      return {};

    auto bits = *op_bits;

    if(bits.size() < width)
    {
      const bool is_signed =
        op.type().id() == ID_signedbv || op.type().id() == ID_verilog_signedbv;

      char pad = '0';

      if(is_signed && !bits.empty())
      {
        // sign extension; give up on x/z sign bits
        if(bits.front() != '0' && bits.front() != '1')
          return {};
        pad = bits.front();
      }

      bits.insert(0, width - bits.size(), pad);
    }
    else if(bits.size() > width)
      bits.erase(0, bits.size() - width);

    return bits;
  }
  else
    return {};
}

/*******************************************************************\

Function: verilog_rtl_buildert::is_wildcard_bit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_rtl_buildert::is_wildcard_bit(const irep_idt &case_type, char bit)
{
  // 1800-2017 12.5.1: the case items of a plain 'case' statement are
  // compared using 4-state equality, i.e., x and z in a case item are
  // not wildcards. Only casex and casez have wildcards: casez treats
  // z (and ?) bits in a case item as wildcards, whereas casex treats
  // x, z (and ?) bits as wildcards.
  if(case_type == ID_verilog_casex)
    return bit == 'x' || bit == 'z' || bit == '?';
  else if(case_type == ID_verilog_casez)
    return bit == 'z' || bit == '?';
  else
    return false;
}

/*******************************************************************\

Function: verilog_rtl_buildert::case_comparison

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_rtl_buildert::case_comparison(
  const irep_idt &case_type,
  const exprt &case_operand,
  const exprt &pattern)
{
  PRECONDITION(
    case_type == ID_verilog_case || case_type == ID_verilog_casex ||
    case_type == ID_verilog_casez);

  // The type checker gives the pattern the max type,
  // per 1800-2017 12.5.
  const typet &pattern_type = pattern.type();

  // We need to take care of the wildcards in the pattern, which
  // depend on the kind of the case statement.
  auto bits_opt = pattern_bits(pattern);

  if(bits_opt.has_value())
  {
    // We are using masking based on the pattern: the wildcard bits
    // are masked out, and the remaining bits are compared.
    auto &bits = *bits_opt;
    auto width = bits.size();

    mp_integer mask = 0, comparison_value = 0;
    bool wildcards = false, four_state = false;

    for(std::size_t bit = 0; bit < width; bit++)
    {
      char bit_char = bits[width - 1 - bit];

      if(is_wildcard_bit(case_type, bit_char))
        wildcards = true;
      else if(bit_char == '0' || bit_char == '1')
      {
        mask += mp_integer{1} << bit;

        if(bit_char == '1')
          comparison_value += mp_integer{1} << bit;
      }
      else
      {
        // An x or z bit that is not a wildcard: such a bit is
        // compared using 4-state equality.
        four_state = true;
      }
    }

    if(wildcards && four_state)
    {
      // The case item has both wildcard bits and x or z bits that are
      // not wildcards. The values of the transition system are
      // two-valued, and hence the x or z bits never match.
      return false_exprt{};
    }

    if(wildcards)
    {
      auto mask_type = unsignedbv_typet{width};

      auto case_operand_casted =
        typecast_exprt::conditional_cast(case_operand, mask_type);

      return equal_exprt{
        bitand_exprt{case_operand_casted, from_integer(mask, mask_type)},
        from_integer(comparison_value, mask_type)};
    }

    // No wildcards: fall through to the comparison below, which is
    // a 4-state comparison when the pattern is four-valued.
  }
  else if(is_aval_bval(pattern_type))
  {
    // We are using masking based on the pattern.
    // The aval is the comparison value, and the
    // negation of bval is the mask.
    auto pattern_aval = ::aval(pattern);
    auto pattern_bval = ::bval(pattern);

    // The wildcard bits depend on the kind of the case statement:
    // in the aval/bval encoding, a bit is x when bval=1 and aval=0,
    // and z when bval=1 and aval=1.
    exprt keep_mask;

    if(case_type == ID_verilog_casex)
    {
      // Any bit with bval=1, i.e., x or z, is a wildcard.
      keep_mask = bitnot_exprt{pattern_bval};
    }
    else if(case_type == ID_verilog_casez)
    {
      // Only z bits, i.e., bval=1 and aval=1, are wildcards.
      keep_mask = bitnot_exprt{bitand_exprt{pattern_bval, pattern_aval}};
    }
    else
    {
      // Plain case: no wildcards, compare all bits.
      keep_mask = to_bv_type(pattern_aval.type()).all_ones_expr();
    }

    auto case_operand_lowered = typecast_exprt::conditional_cast(
      case_operand, aval_bval_underlying(pattern_type));
    auto operand_aval =
      typecast_exprt{::aval(case_operand_lowered), pattern_aval.type()};
    auto operand_bval =
      typecast_exprt{::bval(case_operand_lowered), pattern_bval.type()};

    // On the compared bits, require 4-state equality, i.e., both the
    // aval and the bval have to match.
    return and_exprt{
      equal_exprt{
        bitand_exprt{operand_aval, keep_mask},
        bitand_exprt{pattern_aval, keep_mask}},
      equal_exprt{
        bitand_exprt{operand_bval, keep_mask},
        bitand_exprt{pattern_bval, keep_mask}}};
  }

  // 2-valued comparison
  exprt case_operand_casted =
    typecast_exprt::conditional_cast(case_operand, pattern_type);

  return equal_exprt{case_operand_casted, pattern};
}

/*******************************************************************\

Function: verilog_rtl_buildert::case_values

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_rtl_buildert::case_values(
  const irep_idt &case_type,
  const exprt &values,
  const exprt &case_operand,
  statet &state)
{
  if(values.id() == ID_default)
    return true_exprt{};

  exprt::operandst disjuncts;

  disjuncts.reserve(values.operands().size());

  // The patterns may refer to elaboration-time constants, e.g.
  // parameters, which are substituted so that the wildcard bits
  // of the pattern are known.
  for(auto &pattern : values.operands())
    disjuncts.push_back(
      case_comparison(case_type, case_operand, substitute(pattern, state)));

  return disjunction(disjuncts);
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_case

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::build_case(
  const verilog_case_statement_baset &statement,
  statet &state,
  const framest &frames)
{
  if(statement.operands().size() < 1)
  {
    throw errort().with_location(statement.source_location())
      << "case statement expected to have at least one operand";
  }

  auto case_operand = substitute(statement.case_operand(), state);

  // We convert the case statement into an if-then-else chain,
  // and any 'default' becomes the final 'else'.
  std::optional<verilog_statementt> default_case;

  for(std::size_t i = 1; i < statement.operands().size(); i++)
  {
    auto &case_item = to_verilog_case_item(statement.operands()[i]);

    if(case_item.is_default())
      default_case = case_item.case_statement();
  }

  std::optional<verilog_statementt> chain = std::move(default_case);

  // Iterate over the case items in reverse to build the chain
  // inside out.
  for(std::size_t i = statement.operands().size(); i >= 2; i--)
  {
    auto &case_item = to_verilog_case_item(statement.operands()[i - 1]);

    if(case_item.is_default())
      continue;

    auto cond =
      case_values(statement.id(), case_item.case_value(), case_operand, state);

    if(chain.has_value())
    {
      chain = verilog_ift{
        std::move(cond), case_item.case_statement(), std::move(*chain)};
    }
    else
      chain = verilog_ift{std::move(cond), case_item.case_statement()};
  }

  if(chain.has_value())
    build_statement(*chain, state, frames);
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_incdec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::build_incdec(
  const verilog_statementt &statement,
  statet &state)
{
  if(statement.operands().size() != 1)
  {
    throw errort().with_location(statement.source_location())
      << statement.id() << " expected to have one operand";
  }

  auto &op = to_unary_expr(statement).op();

  const bool increment =
    statement.id() == ID_preincrement || statement.id() == ID_postincrement;

  // Per 1800-2017 11.4.2, the increment and decrement operators
  // behave as blocking assignments.
  auto one = from_integer(1, op.type());

  exprt rhs;

  if(increment)
    rhs = plus_exprt{op, one};
  else
    rhs = minus_exprt{op, one};

  verilog_blocking_assignt assignment{op, std::move(rhs)};
  assignment.add_source_location() = statement.source_location();

  build_assign(assignment, state, true);
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_for

  Inputs:

 Outputs:

 Purpose: Unrolls the loop. The loop guard must evaluate to a
          constant in every iteration.

\*******************************************************************/

void verilog_rtl_buildert::build_for(
  const verilog_fort &statement,
  statet &state,
  const framest &frames)
{
  // the initialization: assignments or declarations with values
  for(auto &init : statement.initialization())
  {
    if(
      init.id() == ID_verilog_blocking_assign ||
      init.id() == ID_verilog_non_blocking_assign)
    {
      build_statement(init, state, frames);
    }
    else if(init.id() == ID_decl)
    {
      // turn into blocking assignments
      for(auto &declarator : to_verilog_decl(init).declarators())
      {
        DATA_INVARIANT(
          declarator.value().is_not_nil(),
          "for-init declarator must have value");
        assign_to(
          declarator.symbol_expr(),
          substitute(declarator.value(), state),
          state,
          true);
      }
    }
    else
    {
      throw errort().with_location(init.source_location())
        << "unexpected initialization in for loop";
    }
  }

  // the frame for the break and continue statements of this loop
  loop_framet loop_frame;
  framest body_frames{&loop_frame, frames.tf};

  while(true)
  {
    loop_frame.continue_states.clear();

    auto guard = simplify_expr(
      fold_system_functions(substitute(statement.condition(), state)), ns);

    if(guard.is_false())
      break;

    if(!guard.is_true())
    {
      throw errort().with_location(statement.condition().source_location())
        << "RTL construction failed to evaluate loop guard: `"
        << to_string(statement.condition()) << '\'';
    }

    // execute the body
    build_statement(statement.body(), state, body_frames);

    // merge in edges from 'continue' statements, if any
    for(auto &continue_state : loop_frame.continue_states)
    {
      statet current(state);
      merge(conjunction(continue_state.guard), continue_state, current, state);
    }

    // execute the step statement
    build_statement(statement.inc_statement(), state, body_frames);
  }

  // Merge in edges from 'break' statements, if any. These come
  // in program order, hence process in reverse order.
  auto &break_states = loop_frame.break_states;

  for(auto state_it = break_states.rbegin(); state_it != break_states.rend();
      ++state_it)
  {
    statet current(state);
    merge(conjunction(state_it->guard), *state_it, current, state);
  }
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_function_call

  Inputs:

 Outputs:

 Purpose: Tasks and functions called as a statement are inlined.

\*******************************************************************/

void verilog_rtl_buildert::build_function_call(
  const verilog_function_callt &call,
  statet &state,
  const framest &frames)
{
  if(call.is_system_function_call())
  {
    // system tasks such as $display do not contribute
    // to the RTL representation
    return;
  }

  auto &function = to_symbol_expr(call.function());
  const symbolt &symbol = ns.lookup(function.get_identifier());

  if(symbol.type.id() != ID_code)
  {
    throw errort().with_location(call.source_location())
      << "expected function or task as first operand";
  }

  // the local symbols of the function or task are not part
  // of the RTL representation
  cycle_local_prefixes.insert(id2string(symbol.name) + '.');

  auto &code_type = to_code_type(symbol.type);
  auto &parameters = code_type.parameters();
  auto &actuals = call.arguments();

  if(parameters.size() != actuals.size())
  {
    throw errort().with_location(call.source_location())
      << "wrong number of arguments";
  }

  // the frame for the return statements of this call
  tf_framet tf_frame;
  framest body_frames{frames.loop, &tf_frame};

  // remember the guard
  auto entry_guard = state.guard;

  // do assignments to input parameters
  for(std::size_t i = 0; i < parameters.size(); i++)
  {
    if(parameters[i].get_bool(ID_input))
    {
      const symbolt &parameter_symbol =
        ns.lookup(parameters[i].get_identifier());
      assign_to(
        parameter_symbol.symbol_expr(),
        substitute(actuals[i], state),
        state,
        true);
    }
  }

  // the body
  for(auto &body_statement : symbol.value.operands())
    build_statement(to_verilog_statement(body_statement), state, body_frames);

  // merge in edges from 'return' statements, if any
  for(auto &return_state : tf_frame.return_states)
  {
    statet current(state);
    merge(conjunction(return_state.guard), return_state, current, state);
  }

  // restore the guard
  state.guard = std::move(entry_guard);

  // do assignments to output parameters
  for(std::size_t i = 0; i < parameters.size(); i++)
  {
    if(parameters[i].get_bool(ID_output))
    {
      const symbolt &parameter_symbol =
        ns.lookup(parameters[i].get_identifier());
      assign_to(
        actuals[i],
        substitute(parameter_symbol.symbol_expr(), state),
        state,
        true);
    }
  }
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::build_check(
  const verilog_assert_assume_cover_statementt &statement,
  const irep_idt &label,
  statet &state)
{
  auto kind_opt = property_kind(statement.id());
  CHECK_RETURN(kind_opt.has_value());

  auto condition = substitute(statement.condition(), state);

  // apply the path condition, if any
  if(!state.guard.empty())
  {
    condition = verilog_implies_exprt{
      conjunction(state.guard),
      typecast_exprt::conditional_cast(std::move(condition), bool_typet{})};
  }

  // The type checker sets the base name for labeled property
  // statements; immediate checks get the label of the enclosing
  // labeled statement, if any.
  auto property_label =
    statement.base_name().empty() ? label : statement.base_name();

  rtl.properties.emplace_back(
    *kind_opt,
    property_context,
    statement.identifier(),
    property_label,
    std::move(condition),
    statement.condition());

  rtl.properties.back().is_sequence =
    statement.id() == ID_verilog_cover_sequence;
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_statement

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::build_statement(
  const verilog_statementt &statement,
  statet &state,
  const framest &frames)
{
  if(statement.id() == ID_block)
  {
    for(auto &block_statement : to_verilog_block(statement).statements())
      build_statement(block_statement, state, frames);
  }
  else if(statement.id() == ID_verilog_blocking_assign)
  {
    build_assign(to_verilog_assign(statement), state, true);
  }
  else if(statement.id() == ID_verilog_blocking_assign_plus)
    build_compound_assign(to_verilog_assign(statement), state, ID_plus);
  else if(statement.id() == ID_verilog_blocking_assign_minus)
    build_compound_assign(to_verilog_assign(statement), state, ID_minus);
  else if(statement.id() == ID_verilog_blocking_assign_mult)
    build_compound_assign(to_verilog_assign(statement), state, ID_mult);
  else if(statement.id() == ID_verilog_blocking_assign_div)
    build_compound_assign(to_verilog_assign(statement), state, ID_div);
  else if(statement.id() == ID_verilog_blocking_assign_mod)
    build_compound_assign(to_verilog_assign(statement), state, ID_mod);
  else if(statement.id() == ID_verilog_blocking_assign_bitand)
    build_compound_assign(to_verilog_assign(statement), state, ID_bitand);
  else if(statement.id() == ID_verilog_blocking_assign_bitor)
    build_compound_assign(to_verilog_assign(statement), state, ID_bitor);
  else if(statement.id() == ID_verilog_blocking_assign_bitxor)
    build_compound_assign(to_verilog_assign(statement), state, ID_bitxor);
  else if(statement.id() == ID_verilog_blocking_assign_lshr)
    build_compound_assign(to_verilog_assign(statement), state, ID_lshr);
  else if(statement.id() == ID_verilog_blocking_assign_lshl)
    build_compound_assign(to_verilog_assign(statement), state, ID_shl);
  else if(statement.id() == ID_verilog_blocking_assign_ashr)
    build_compound_assign(to_verilog_assign(statement), state, ID_ashr);
  else if(statement.id() == ID_verilog_blocking_assign_ashl)
    build_compound_assign(to_verilog_assign(statement), state, ID_shl);
  else if(statement.id() == ID_verilog_non_blocking_assign)
  {
    build_assign(to_verilog_assign(statement), state, false);
  }
  else if(statement.id() == ID_if)
  {
    build_if(to_verilog_if(statement), state, frames);
  }
  else if(
    statement.id() == ID_verilog_case || statement.id() == ID_verilog_casex ||
    statement.id() == ID_verilog_casez)
  {
    build_case(to_verilog_case_statement_base(statement), state, frames);
  }
  else if(
    statement.id() == ID_preincrement || statement.id() == ID_predecrement ||
    statement.id() == ID_postincrement || statement.id() == ID_postdecrement)
  {
    build_incdec(statement, state);
  }
  else if(statement.id() == ID_for)
  {
    build_for(to_verilog_for(statement), state, frames);
  }
  else if(statement.id() == ID_break)
  {
    if(frames.loop == nullptr)
    {
      throw errort().with_location(statement.source_location())
        << "break outside of loop";
    }

    frames.loop->break_states.push_back(state);

    // the rest of the path is dead
    state.guard.push_back(false_exprt{});
  }
  else if(statement.id() == ID_continue)
  {
    if(frames.loop == nullptr)
    {
      throw errort().with_location(statement.source_location())
        << "continue outside of loop";
    }

    frames.loop->continue_states.push_back(state);

    // the rest of the path is dead
    state.guard.push_back(false_exprt{});
  }
  else if(statement.id() == ID_return)
  {
    if(frames.tf == nullptr)
    {
      throw errort().with_location(statement.source_location())
        << "return outside of function or task";
    }

    auto &return_statement = to_verilog_return(statement);

    if(return_statement.has_value())
    {
      if(!frames.tf->return_value.has_value())
      {
        throw errort().with_location(statement.source_location())
          << "return with value requires a function";
      }

      assign_to(
        *frames.tf->return_value,
        substitute(return_statement.value(), state),
        state,
        true);
    }

    frames.tf->return_states.push_back(state);

    // the rest of the path is dead
    state.guard.push_back(false_exprt{});
  }
  else if(statement.id() == ID_function_call)
  {
    build_function_call(to_verilog_function_call(statement), state, frames);
  }
  else if(statement.id() == ID_forever)
  {
    throw errort().with_location(statement.source_location())
      << "cannot synthesize `forever'";
  }
  else if(statement.id() == ID_procedural_continuous_assign)
  {
    throw errort().with_location(statement.source_location())
      << "synthesis of procedural continuous assignment not supported";
  }
  else if(statement.id() == ID_verilog_expect_property)
  {
    throw errort().with_location(statement.source_location())
      << "synthesis of expect property not supported";
  }
  else if(statement.id() == ID_delay)
  {
    // the delay is ignored
    build_statement(to_verilog_delay(statement).body(), state, frames);
  }
  else if(statement.id() == ID_decl)
  {
    // Block-level declarations do not contribute statements to the
    // RTL representation; the values of declarators yield the
    // initial state. The declared variables are recorded.
    auto &decl = to_verilog_decl(statement);
    auto decl_class = decl.get_class();

    if(
      decl_class != ID_function && decl_class != ID_task &&
      decl_class != ID_typedef)
    {
      for(auto &declarator : decl.declarators())
        record_variable(declarator.symbol_expr().get_identifier());
    }
  }
  else if(statement.id() == ID_verilog_label_statement)
  {
    auto &label_statement = to_verilog_label_statement(statement);
    auto &sub_statement = label_statement.statement();

    // the label is passed on to assert/assume/cover statements
    if(is_check(sub_statement.id()))
    {
      build_check(
        to_verilog_assert_assume_cover_statement(sub_statement),
        label_statement.label(),
        state);
    }
    else
      build_statement(sub_statement, state, frames);
  }
  else if(is_check(statement.id()))
  {
    build_check(
      to_verilog_assert_assume_cover_statement(statement), irep_idt{}, state);
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

    // function and task locals are not part of the RTL representation
    if(is_cycle_local(identifier))
      continue;

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
    // Guard-less always constructs are only supported when they
    // consist of checks only, e.g. always assert(...), which are
    // recorded as properties.
    if(!is_check_only(*body))
    {
      throw errort().with_location(always.source_location())
        << "assignment in 'always' context without event guard";
    }
  }

  statet state;

  auto old_context = property_context;
  property_context = verilog_rtl_propertyt::contextt::ALWAYS;

  build_statement(*body, state, framest{});

  property_context = old_context;

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

    assign_to(
      equal_expr.lhs(), substitute(equal_expr.rhs(), state), state, false);

    commit(state, kindt::WIRE, module_item.source_location());
  }
}

/*******************************************************************\

Function: verilog_rtl_buildert::supply_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_rtl_buildert::supply_value(
  const irep_idt &decl_class,
  const typet &type)
{
  if(type.id() == ID_array)
  {
    auto &array_type = to_array_type(type);
    auto element = supply_value(decl_class, array_type.element_type());
    return array_of_exprt{std::move(element), array_type};
  }
  else if(type.id() == ID_unsignedbv)
  {
    if(decl_class == ID_supply0)
      return from_integer(0, type);
    else
      return from_integer(
        power(2, to_unsignedbv_type(type).get_width()) - 1, type);
  }
  else if(type.id() == ID_signedbv)
  {
    if(decl_class == ID_supply0)
      return from_integer(0, type);
    else
      return from_integer(-1, type);
  }
  else if(type.id() == ID_bool)
  {
    if(decl_class == ID_supply0)
      return false_exprt{};
    else
      return true_exprt{};
  }
  else
  {
    throw errort() << decl_class << " for unexpected type";
  }
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_module_item_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::build_module_item_decl(
  const verilog_declt &module_item)
{
  auto decl_class = module_item.get_class();

  // Function and task declarations are inlined at their call sites.
  // Type declarations do not contribute to the RTL representation.
  if(
    decl_class == ID_function || decl_class == ID_task ||
    decl_class == ID_typedef)
  {
    return;
  }

  // supply0 and supply1 nets are wired to a constant
  if(decl_class == ID_supply0 || decl_class == ID_supply1)
  {
    for(auto &declarator : module_item.declarators())
    {
      DATA_INVARIANT(declarator.id() == ID_declarator, "must have declarator");

      auto lhs = declarator.symbol_expr();
      const symbolt &symbol = ns.lookup(lhs.get_identifier());

      if(!symbol.is_lvalue)
      {
        auto value = supply_value(decl_class, lhs.type());
        statet state;
        assign_to(lhs, std::move(value), state, false);
        commit(state, kindt::WIRE, declarator.source_location());
      }
    }
  }

  for(auto &declarator : module_item.declarators())
  {
    DATA_INVARIANT(declarator.id() == ID_declarator, "must have declarator");

    record_variable(declarator.symbol_expr().get_identifier());

    if(declarator.has_value())
    {
      auto lhs = declarator.symbol_expr();

      // Assignments to reals are silently ignored.
      if(lhs.type().id() == ID_verilog_realtime)
        continue;

      const symbolt &symbol = ns.lookup(lhs.get_identifier());

      if(!symbol.is_lvalue)
      {
        // a net declaration with a value is a continuous assignment
        statet state;
        assign_to(lhs, substitute(declarator.value(), state), state, false);
        commit(state, kindt::WIRE, declarator.source_location());
      }
      else
      {
        // a variable declaration with a value yields an initial value
        statet state;
        write_slice(
          rtl.initial_values[lhs.get_identifier()],
          whole_slice(lhs),
          substitute(declarator.value(), state));
      }
    }
  }
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_interface_port_connection

  Inputs:

 Outputs:

 Purpose: Connects the members of an interface port to the members
          of the bound interface instance.

\*******************************************************************/

void verilog_rtl_buildert::build_interface_port_connection(
  const module_typet::portt &port,
  const exprt &value)
{
  if(value.id() != ID_symbol)
    return;

  auto &bound_instance_id = to_symbol_expr(value).get_identifier();
  auto port_prefix = id2string(port.identifier()) + ".";
  auto bound_prefix = id2string(bound_instance_id) + ".";

  for(auto &entry : symbol_table.symbols)
  {
    auto id = id2string(entry.first);
    if(
      id.size() > port_prefix.size() &&
      id.substr(0, port_prefix.size()) == port_prefix &&
      id.find('.', port_prefix.size()) == std::string::npos)
    {
      auto member_name = id.substr(port_prefix.size());
      auto bound_id = bound_prefix + member_name;

      const symbolt *bound_symbol;
      if(ns.lookup(bound_id, bound_symbol))
        continue;

      if(bound_symbol->type.id() == ID_verilog_module_instance)
        continue;

      symbol_exprt port_member{entry.first, entry.second.type};
      symbol_exprt bound_member{bound_id, bound_symbol->type};

      rtl.constraints.push_back(
        equal_exprt{std::move(port_member), std::move(bound_member)});
    }
  }
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_port_connection

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::build_port_connection(
  const module_typet::portt &port,
  const exprt &value,
  const irep_idt &instance_identifier,
  const source_locationt &source_location)
{
  // Interface ports connect the members of the port's interface
  // to the members of the bound interface instance.
  if(port.type().id() == ID_verilog_module_instance)
  {
    build_interface_port_connection(port, value);
    return;
  }

  symbol_exprt port_symbol{port.identifier(), port.type()};

  // Convert the rhs to the type of the lhs, as an assignment would.
  // Note that the types need not match. Narrowing to a one-bit net must
  // take the least-significant bit, as in assignment_conversion; a plain
  // typecast to bool would instead compute a (!= 0) reduction.
  auto narrowing_cast = [](exprt src, const typet &dest_type) -> exprt
  {
    if(dest_type.id() == ID_bool && src.type().id() != ID_bool)
      return extractbit_exprt{std::move(src), from_integer(0, integer_typet{})};
    else
      return typecast_exprt::conditional_cast(src, dest_type);
  };

  // Much like
  //   assign port = value for an input, and
  //   assign value = port for an output.
  // These are constraints rather than wire definitions, since
  // a net may have multiple drivers.
  exprt lhs, rhs;

  if(port.output())
  {
    lhs = value;
    rhs = narrowing_cast(port_symbol, value.type());
  }
  else
  {
    lhs = port_symbol;
    rhs = narrowing_cast(value, port_symbol.type());
  }

  statet state;
  record_forced(lhs, instance_identifier);
  rtl.constraints.push_back(equal_exprt{
    substitute(std::move(lhs), state), substitute(std::move(rhs), state)});
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_port_connections

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::build_port_connections(
  const verilog_instt::instancet &instance,
  const symbolt &module_symbol)
{
  if(instance.connections().empty())
    return;

  auto &module_type = to_module_type(module_symbol.type);

  if(instance.named_port_connections())
  {
    const auto &ports = module_type.ports();
    auto port_map = module_type.port_map();

    // no requirement that all ports are connected
    for(const auto &connection : instance.connections())
    {
      if(connection.id() == ID_verilog_wildcard_port_connection)
      {
        throw errort{}.with_location(connection.source_location())
          << "no support for wildcard port connection";
      }

      auto &named_connection = to_verilog_named_port_connection(connection);
      auto port_it =
        port_map.find(to_symbol_expr(named_connection.port()).identifier());
      CHECK_RETURN(port_it != port_map.end());
      auto &port = port_it->second;
      const exprt &value = named_connection.value();

      if(value.is_not_nil())
      {
        build_port_connection(
          port, value, instance.identifier(), instance.source_location());
      }
    }

    std::set<irep_idt> connected_ports;

    for(const auto &connection : instance.connections())
    {
      auto &named_connection = to_verilog_named_port_connection(connection);
      connected_ports.insert(
        to_symbol_expr(named_connection.port()).identifier());
    }

    // unconnected inputs may be given a default value
    for(auto &port : ports)
      if(port.input())
      {
        auto identifier = port.identifier();
        if(connected_ports.find(identifier) == connected_ports.end())
        {
          auto &port_symbol = ns.lookup(identifier);
          if(port_symbol.value.is_not_nil())
          {
            build_port_connection(
              port,
              port_symbol.value,
              instance.identifier(),
              instance.source_location());
          }
        }
      }
  }
  else // just a list without names
  {
    const auto &ports = module_type.ports();

    if(instance.connections().size() != ports.size())
    {
      throw errort().with_location(instance.source_location())
        << "wrong number of ports: expected " << ports.size() << " but got "
        << instance.connections().size();
    }

    auto p_it = ports.begin();

    for(const auto &connection : instance.connections())
    {
      // Unconnected ports are left unconstrained.
      if(connection.is_not_nil())
      {
        build_port_connection(
          *p_it, connection, instance.identifier(), instance.source_location());
      }

      p_it++;
    }
  }
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_instances

  Inputs:

 Outputs:

 Purpose: Module instances are included recursively; the port
          connections become wire definitions or constraints.

\*******************************************************************/

void verilog_rtl_buildert::build_instances(const verilog_instt &module_item)
{
  for(auto &instance : module_item.instances())
  {
    const symbolt &module_symbol = ns.lookup(instance.module_identifier());

    // the instantiated module, recursively
    build_module(module_symbol);

    // the port connections
    build_port_connections(instance, module_symbol);
  }
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_gate_instances

  Inputs:

 Outputs:

 Purpose: Primitive gates. 1800-2017 chapter 28.

\*******************************************************************/

void verilog_rtl_buildert::build_gate_instances(
  const verilog_inst_builtint &module_item)
{
  const irep_idt &module = module_item.module_base_name();

  for(auto &instance : module_item.instances())
  {
    if(
      module == ID_bufif0 || module == ID_bufif1 || module == ID_notif0 ||
      module == ID_notif1 || module == ID_nmos || module == ID_pmos ||
      module == ID_rnmos || module == ID_rpmos || module == "tranif0" ||
      module == "tranif1" || module == "rtranif1" || module == "rtranif0" ||
      module == "tran" || module == "rtran")
    {
      // add to the general constraints
      exprt constraint = instance;
      constraint.id("verilog-primitive-module");
      constraint.type() = bool_typet{};
      constraint.set(ID_module, module);
      rtl.constraints.push_back(std::move(constraint));
    }
    else if(
      module == ID_and || module == ID_nand || module == ID_or ||
      module == ID_nor || module == ID_xor || module == ID_xnor)
    {
      // One output, one or more inputs.
      DATA_INVARIANT(
        instance.connections().size() >= 2,
        "binary primitive gates should have at least two connections");

      auto &connections = instance.connections();
      auto &output = connections[0];

      irep_idt id = instance.type().id() == ID_bool
                      ? module
                      : irep_idt{"bit" + id2string(module)};

      exprt::operandst operands;

      // iterate over the gate inputs
      for(std::size_t i = 1; i < connections.size(); i++)
        operands.push_back(connections[i]);

      auto op = exprt{id, instance.type(), std::move(operands)};

      // a constraint, since a net may have multiple drivers
      statet state;
      rtl.constraints.push_back(
        equal_exprt{output, substitute(std::move(op), state)});
    }
    else if(module == ID_buf || module == ID_not)
    {
      DATA_INVARIANT(
        instance.connections().size() >= 2,
        "buf/not gates should have at least two connections");

      // May have multiple outputs. The input is the last connection.
      auto &input = instance.connections().back();

      exprt rhs;

      if(module == ID_not)
      {
        if(input.type().id() == ID_bool)
          rhs = not_exprt{input};
        else
          rhs = bitnot_exprt{input};
      }
      else
        rhs = input;

      for(std::size_t i = 0; i < instance.connections().size() - 1; i++)
      {
        statet state;
        rtl.constraints.push_back(
          equal_exprt{instance.connections()[i], substitute(rhs, state)});
      }
    }
    else
    {
      throw errort().with_location(module_item.source_location())
        << "primitive gate `" << module
        << "' is not supported by RTL construction";
    }
  }
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_module

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::build_module(const symbolt &module_symbol)
{
  // The module must be type checked, but not yet synthesized.
  if(module_symbol.value.id() != ID_verilog_module)
  {
    throw errort() << "module `" << module_symbol.name
                   << "' is not a type-checked Verilog module";
  }

  auto &module_items =
    to_verilog_module_expr(module_symbol.value).module_items();

  // Record the port-declared variables, since ANSI-style port
  // declarations do not appear as decl module items.
  // Not done for $root, which uses the identifiers of its submodules.
  if(module_symbol.name != verilog_root_module_identifier())
  {
    for(auto &port : to_module_type(module_symbol.type).ports())
      record_variable(port.identifier());
  }

  // Modules have their own 'default disable iff'.
  auto old_default_disable_iff = std::move(default_disable_iff);
  default_disable_iff = {};

  for(auto &module_item : module_items)
    if(module_item.id() == ID_verilog_default_disable)
    {
      if(default_disable_iff.has_value())
      {
        throw errort().with_location(module_item.source_location())
          << "default disable iff already set";
      }
      default_disable_iff = to_verilog_default_disable(module_item).cond();
    }

  for(auto &module_item : module_items)
    build_module_item(module_item);

  default_disable_iff = std::move(old_default_disable_iff);
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::build_property(
  const verilog_assert_assume_cover_module_itemt &module_item)
{
  auto kind_opt = property_kind(module_item.id());
  CHECK_RETURN(kind_opt.has_value());

  // substitute elaboration-time constants,
  // and expand function calls
  statet state;
  auto condition = substitute(module_item.condition(), state);

  // apply the default disable iff, if any
  if(default_disable_iff.has_value() && condition.id() != ID_sva_disable_iff)
  {
    condition =
      sva_disable_iff_exprt{*default_disable_iff, std::move(condition)};
  }

  rtl.properties.emplace_back(
    *kind_opt,
    verilog_rtl_propertyt::contextt::MODULE_LEVEL,
    module_item.identifier(),
    module_item.base_name(),
    std::move(condition),
    module_item.condition());

  rtl.properties.back().is_sequence =
    module_item.id() == ID_verilog_cover_sequence;
}

/*******************************************************************\

Function: verilog_rtl_buildert::build_initial

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_rtl_buildert::build_initial(const verilog_initialt &module_item)
{
  auto old_context = property_context;
  property_context = verilog_rtl_propertyt::contextt::INITIAL;

  statet state;
  build_statement(module_item.statement(), state, framest{});

  property_context = old_context;

  // record the assigned values as initial values
  for(auto &value_entry : state.values)
  {
    auto &identifier = value_entry.first;

    if(is_cycle_local(identifier))
      continue;

    auto &slice_map = rtl.initial_values[identifier];

    for(auto &slice_entry : value_entry.second)
      write_slice(slice_map, slice_entry.first, slice_entry.second);
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
  else if(module_item.id() == ID_decl)
  {
    build_module_item_decl(to_verilog_decl(module_item));
  }
  else if(
    module_item.id() == ID_verilog_assert_property ||
    module_item.id() == ID_verilog_assume_property ||
    module_item.id() == ID_verilog_restrict_property ||
    module_item.id() == ID_verilog_cover_property ||
    module_item.id() == ID_verilog_cover_sequence)
  {
    build_property(to_verilog_assert_assume_cover_module_item(module_item));
  }
  else if(module_item.id() == ID_verilog_assertion_item)
  {
    // A deferred immediate assertion outside procedural code,
    // e.g. a1: assert final (a == b); these behave like checks
    // in an always_comb process (1800-2017 16.4.3).
    auto old_context = property_context;
    property_context = verilog_rtl_propertyt::contextt::ALWAYS;

    statet state;
    build_statement(
      to_verilog_assertion_item(module_item).statement(), state, framest{});

    property_context = old_context;
  }
  else if(module_item.id() == ID_initial)
  {
    build_initial(to_verilog_initial(module_item));
  }
  else if(module_item.id() == ID_inst)
  {
    build_instances(to_verilog_inst(module_item));
  }
  else if(module_item.id() == ID_inst_builtin)
  {
    build_gate_instances(to_verilog_inst_builtin(module_item));
  }
  else if(module_item.id() == ID_generate_block)
  {
    // These have their own 'default disable iff'.
    auto old_default_disable_iff = std::move(default_disable_iff);
    default_disable_iff = {};

    auto &block = to_verilog_generate_block(module_item);

    for(auto &block_item : block.module_items())
      if(block_item.id() == ID_verilog_default_disable)
        default_disable_iff = to_verilog_default_disable(block_item).cond();

    for(auto &block_item : block.module_items())
      build_module_item(block_item);

    default_disable_iff = std::move(old_default_disable_iff);
  }
  else
  {
    // Parameter declarations, default clocking/disable,
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

  build_module(module_symbol);

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

  for(auto &initial_entry : initial_values)
  {
    for(auto &slice_entry : initial_entry.second)
    {
      auto &slice = slice_entry.first;

      out << strip_verilog_prefix(initial_entry.first) << '[' << slice.higher
          << ':' << slice.lower
          << "] initial value: " << expr2verilog(slice_entry.second, ns)
          << '\n';
    }
  }

  for(auto &constraint : constraints)
    out << "constraint: " << expr2verilog(constraint, ns) << '\n';

  for(auto &property : properties)
  {
    switch(property.kind)
    {
    case verilog_rtl_propertyt::kindt::ASSERT:
      out << "assert";
      break;
    case verilog_rtl_propertyt::kindt::ASSUME:
      out << "assume";
      break;
    case verilog_rtl_propertyt::kindt::COVER:
      out << "cover";
      break;
    }

    if(!property.label.empty())
      out << ' ' << property.label;

    out << ": " << expr2verilog(property.condition, ns) << '\n';
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
    standard, symbol_table, ns, module_identifier, message_handler);

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

    throw ebmc_errort{}.with_exit_code(2);
  }
}
