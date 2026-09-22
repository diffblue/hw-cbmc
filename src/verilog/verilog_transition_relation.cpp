/*******************************************************************\

Module: Verilog Transition Relation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_transition_relation.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/expr_util.h>
#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/symbol_table_base.h>

#include <ebmc/ebmc_error.h>

#include "expr2verilog.h"
#include "sva_expr.h"
#include "verilog_bits.h"
#include "verilog_expr.h"
#include "verilog_initializer.h"
#include "verilog_lowering.h"
#include "verilog_rtl.h"
#include "verilog_typecheck_base.h"
#include "verilog_typecheck_expr.h"

#include <algorithm>

/*******************************************************************\

   Class: verilog_transition_relationt

 Purpose: Creates the transition relation for a module from its
          RTL representation.

\*******************************************************************/

class verilog_transition_relationt : public verilog_typecheck_baset
{
public:
  verilog_transition_relationt(
    verilog_standardt _standard,
    symbol_table_baset &_symbol_table,
    const namespacet &_ns,
    const irep_idt &_module,
    bool _ignore_initial,
    bool _initial_zero,
    message_handlert &_message_handler)
    : verilog_typecheck_baset(_standard, _ns, _message_handler),
      module(_module),
      symbol_table(_symbol_table),
      ignore_initial(_ignore_initial),
      initial_zero(_initial_zero),
      message_handler(_message_handler)
  {
  }

  void typecheck() override
  {
  }

  // throws errort on error
  transt convert();

protected:
  const irep_idt module;
  symbol_table_baset &symbol_table;
  bool ignore_initial, initial_zero;
  message_handlert &message_handler;

  std::size_t nondet_count = 0;

  using kindt = verilog_rtl_definitiont::kindt;

  void convert_definitions(const verilog_rtlt &, transt &);
  void convert_initial_values(const verilog_rtlt &, transt &);
  void convert_constraints(const verilog_rtlt &, transt &);
  void convert_properties(const verilog_rtlt &);

  /// compose the value of the given symbol from the given slices;
  /// slices that are not defined get the given default value
  exprt compose(
    const verilog_rtlt::slice_mapt &,
    const symbol_exprt &,
    const std::function<exprt(const verilog_rtl_slicet &)> &default_value);

  exprt compose_values(
    const std::map<verilog_rtl_slicet, exprt> &,
    const symbol_exprt &,
    const std::function<exprt(const verilog_rtl_slicet &)> &default_value);

  /// the value of the sub-slice of a slice value
  static exprt extract_range(
    const exprt &value,
    const verilog_rtl_slicet &from,
    const verilog_rtl_slicet &sub);

  /// rewrite system function calls, e.g. $past, and then
  /// lower Verilog-specific expressions
  exprt lower(exprt);

  exprt lower_system_functions(exprt);

  /// the symbol, with lowered type
  exprt symbol_expr(const symbolt &, bool next) const;

  /// The width of the entire identifier as a slice. Types without
  /// a fixed number of bits, e.g. chandles, are a single slice.
  static verilog_rtl_slicet whole_slice(const typet &type)
  {
    auto bits_opt = verilog_bits_opt(type);
    if(bits_opt.has_value())
      return verilog_rtl_slicet{0, *bits_opt - 1};
    else
      return verilog_rtl_slicet{0, 0};
  }

  /// replace reads of state-holding variables by their
  /// non-deterministic pre-initial value
  void initial_nondet(exprt &);

  /// remove initial-state constraints that are unused
  /// non-determinism
  static void post_process_initial(exprt &constraints);

  /// replace reads of the given wire in its own definition
  /// by non-determinism
  static void post_process_wire(const irep_idt &identifier, exprt &);

  static void set_default_sequence_semantics(exprt &, bool strong);
};

/*******************************************************************\

Function: verilog_transition_relationt::extract_range

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_transition_relationt::extract_range(
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

Function: verilog_transition_relationt::compose_values

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_transition_relationt::compose_values(
  const std::map<verilog_rtl_slicet, exprt> &slice_values,
  const symbol_exprt &symbol,
  const std::function<exprt(const verilog_rtl_slicet &)> &default_value)
{
  auto whole = whole_slice(symbol.type());
  auto width = whole.width();

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

    // look for a defined slice that contains the fragment
    exprt fragment_value = nil_exprt{};

    for(auto &entry : slice_values)
    {
      if(
        entry.first.lower <= fragment.lower &&
        fragment.higher <= entry.first.higher)
      {
        fragment_value = extract_range(entry.second, entry.first, fragment);
        break;
      }
    }

    if(fragment_value.is_nil())
      fragment_value = default_value(fragment);

    fragments.push_back(std::move(fragment_value));
  }

  DATA_INVARIANT(!fragments.empty(), "must have at least one fragment");

  if(fragments.size() == 1)
    return typecast_exprt::conditional_cast(fragments.front(), symbol.type());

  // concatenations take the most significant operand first
  std::reverse(fragments.begin(), fragments.end());

  auto width_int = numeric_cast_v<std::size_t>(width);

  return typecast_exprt::conditional_cast(
    concatenation_exprt{std::move(fragments), unsignedbv_typet{width_int}},
    symbol.type());
}

/*******************************************************************\

Function: verilog_transition_relationt::compose

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_transition_relationt::compose(
  const verilog_rtlt::slice_mapt &slice_map,
  const symbol_exprt &symbol,
  const std::function<exprt(const verilog_rtl_slicet &)> &default_value)
{
  std::map<verilog_rtl_slicet, exprt> slice_values;

  for(auto &entry : slice_map)
    slice_values.emplace(entry.first, entry.second.value);

  return compose_values(slice_values, symbol, default_value);
}

/*******************************************************************\

Function: verilog_transition_relationt::symbol_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_transition_relationt::symbol_expr(
  const symbolt &symbol,
  bool next) const
{
  exprt result = exprt{next ? ID_next_symbol : ID_symbol, symbol.type};
  result.set(ID_identifier, symbol.name);

  // The type may need to be lowered
  result.type() = verilog_lowering(result.type());

  return result;
}

/*******************************************************************\

Function: verilog_transition_relationt::lower_system_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_transition_relationt::lower_system_functions(exprt expr)
{
  for(auto &op : expr.operands())
    op = lower_system_functions(std::move(op));

  if(expr.id() == ID_typecast)
  {
    // We do some simplification
    if(to_typecast_expr(expr).op().type().id() == ID_integer)
      return simplify_expr(expr, ns);
    return expr;
  }

  if(expr.id() == ID_function_call)
  {
    auto &call = to_function_call_expr(expr);

    if(!call.is_system_function_call())
    {
      throw errort().with_location(expr.source_location())
        << "unexpected function call";
    }

    auto base_name = to_verilog_identifier_expr(call.function()).base_name();

    if(base_name == "$ND")
    {
      std::string identifier =
        id2string(module) + "::nondet::" + std::to_string(nondet_count++);

      auto arguments = call.arguments();
      exprt select_one(
        ID_constraint_select_one, call.type(), std::move(arguments));
      select_one.set(ID_identifier, identifier);
      return select_one.with_source_location(call);
    }
    else if(base_name == "$past")
    {
      auto &what = call.arguments()[0];
      auto ticks = call.arguments().size() < 2
                     ? from_integer(1, integer_typet{})
                     : call.arguments()[1];
      return verilog_past_exprt{what, ticks}.with_source_location(call);
    }
    else if(
      base_name == "$stable" || base_name == "$rose" || base_name == "$fell" ||
      base_name == "$changed")
    {
      DATA_INVARIANT(call.arguments().size() >= 1, "must have argument");
      auto &what = call.arguments()[0];
      auto past = verilog_past_exprt{what, from_integer(1, integer_typet{})}
                    .with_source_location(call);

      auto lsb = [](exprt expr) {
        return extractbit_exprt{
          std::move(expr), from_integer(0, integer_typet{})};
      };

      if(base_name == "$stable")
        return equal_exprt{what, past};
      else if(base_name == "$changed")
        return notequal_exprt{what, past};
      else if(base_name == "$rose")
        return and_exprt{not_exprt{lsb(past)}, lsb(what)};
      else // $fell
        return and_exprt{lsb(past), not_exprt{lsb(what)}};
    }
    else if(base_name == "$countones")
    {
      DATA_INVARIANT(
        call.arguments().size() == 1, "$countones must have one argument");
      return popcount_exprt{call.arguments()[0], call.type()};
    }
    else if(base_name == "$value$plusargs" || base_name == "$test$plusargs")
    {
      // IEEE 1800-2017 section 21.6
      // Return 0, indicating plusarg not found.
      return from_integer(0, call.type()).with_source_location(call);
    }
    else
    {
      // Attempt to constant fold.
      verilog_typecheck_exprt verilog_typecheck_expr(
        standard, false, ns, message_handler);
      auto result =
        verilog_typecheck_expr.elaborate_constant_system_function_call(call);
      if(!result.is_constant())
      {
        throw errort().with_location(call.source_location())
          << "cannot convert system function " << to_string(call.function());
      }

      return result;
    }
  }

  return expr;
}

/*******************************************************************\

Function: verilog_transition_relationt::lower

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_transition_relationt::lower(exprt expr)
{
  // First lower any Verilog-specific expressions, then rewrite
  // the remaining system function calls, e.g. $past.
  return lower_system_functions(verilog_lowering(std::move(expr)));
}

/*******************************************************************\

Function: verilog_transition_relationt::post_process_wire

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_transition_relationt::post_process_wire(
  const irep_idt &identifier,
  exprt &expr)
{
  // look if the wire is used to define itself

  for(auto &op : expr.operands())
    post_process_wire(identifier, op);

  if(expr.id() == ID_symbol && expr.get(ID_identifier) == identifier)
    expr.id(ID_nondet_symbol);
}

/*******************************************************************\

Function: verilog_transition_relationt::initial_nondet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_transition_relationt::initial_nondet(exprt &expr)
{
  for(auto &op : expr.operands())
    initial_nondet(op);

  if(expr.id() == ID_symbol)
  {
    const symbolt *symbol;
    if(!ns.lookup(to_symbol_expr(expr).get_identifier(), symbol))
    {
      if(symbol->is_lvalue)
      {
        // This is a value _before_ the initial state --
        // make it non-deterministic.
        expr.id(ID_nondet_symbol);
        expr.set("initial_value", true);
      }
    }
  }
}

/*******************************************************************\

Function: subexpressions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void subexpressions(const exprt &expr, std::multiset<exprt> &counters)
{
  counters.insert(expr);

  for(auto &op : expr.operands())
    subexpressions(op, counters);
}

/*******************************************************************\

Function: verilog_transition_relationt::post_process_initial

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_transition_relationt::post_process_initial(exprt &constraints)
{
  // look for unused non-determinism constraints

  std::multiset<exprt> counters;

  for(auto &op : constraints.operands())
    subexpressions(op, counters);

  for(auto &op : constraints.operands())
  {
    if(op.id() == ID_equal && op.operands().size() == 2)
    {
      exprt &lhs = to_equal_expr(op).lhs(), &rhs = to_equal_expr(op).rhs();

      if(lhs.id() == ID_symbol && rhs.id() == ID_nondet_symbol)
      {
        if(counters.count(rhs) == 1)
        {
          // not used elsewhere
          op.set(ID_value, ID_true);
        }
      }
    }
  }
}

/*******************************************************************\

Function: verilog_transition_relationt::convert_definitions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_transition_relationt::convert_definitions(
  const verilog_rtlt &rtl,
  transt &trans)
{
  for(auto &identifier_entry : rtl.identifier_map)
  {
    auto &identifier = identifier_entry.first;
    auto &slice_map = identifier_entry.second;

    symbolt &symbol = symbol_table.get_writeable_ref(identifier);
    const auto lowered_type = verilog_lowering(symbol.type);
    const symbol_exprt symbol_expr_raw{identifier, symbol.type};

    // all slices must have the same kind
    bool state_holding = slice_map.begin()->second.is_state_holding();

    for(auto &slice_entry : slice_map)
    {
      if(slice_entry.second.is_state_holding() != state_holding)
      {
        throw errort().with_location(symbol.location)
          << "conflicting assignment types for `" << symbol.display_name()
          << "'";
      }
    }

    if(!state_holding && symbol.is_lvalue)
    {
      // only assigned combinationally -- make it a wire
      warning().source_location = symbol.location;
      warning() << "Making " << symbol.display_name() << " a wire" << eom;
      symbol.is_lvalue = false;
    }

    if(state_holding && !symbol.is_lvalue)
    {
      throw errort().with_location(symbol.location)
        << "clocked assignment to non-variable `" << symbol.display_name()
        << "'";
    }

    auto whole = whole_slice(symbol.type);

    if(state_holding)
    {
      // Slices that are not assigned hold their value.
      auto value = compose(
        slice_map,
        symbol_expr_raw,
        [&symbol_expr_raw, &whole](const verilog_rtl_slicet &fragment)
        { return extract_range(symbol_expr_raw, whole, fragment); });

      auto lowered_value =
        typecast_exprt::conditional_cast(lower(std::move(value)), lowered_type);

      exprt lhs = symbol_expr(symbol, true); // next state

      trans.trans().add_to_operands(
        equal_exprt{std::move(lhs), std::move(lowered_value)});

      // This is a proper state variable.
      symbol.is_state_var = true;
    }
    else
    {
      // Slices that are not assigned are unconstrained.
      exprt nondet = symbol_expr_raw;
      nondet.id(ID_nondet_symbol);

      auto value = compose(
        slice_map,
        symbol_expr_raw,
        [&nondet, &whole](const verilog_rtl_slicet &fragment)
        { return extract_range(nondet, whole, fragment); });

      auto lowered_value =
        typecast_exprt::conditional_cast(lower(std::move(value)), lowered_type);

      // reads of the wire in its own definition are non-determinism
      post_process_wire(identifier, lowered_value);

      exprt lhs = symbol_expr(symbol, false);

      trans.invar().add_to_operands(
        equal_exprt{std::move(lhs), std::move(lowered_value)});
    }
  }
}

/*******************************************************************\

Function: verilog_transition_relationt::convert_initial_values

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_transition_relationt::convert_initial_values(
  const verilog_rtlt &rtl,
  transt &trans)
{
  // Declared variables without a next-state definition
  // hold their value.
  for(auto &identifier : rtl.variables)
  {
    if(rtl.identifier_map.find(identifier) != rtl.identifier_map.end())
      continue;

    symbolt &symbol = symbol_table.get_writeable_ref(identifier);

    if(!symbol.is_lvalue)
      continue; // demoted to a wire

    symbol.is_state_var = true;

    trans.trans().add_to_operands(
      equal_exprt{symbol_expr(symbol, true), symbol_expr(symbol, false)});
  }

  if(ignore_initial)
    return;

  for(auto &initial_entry : rtl.initial_values)
  {
    auto &identifier = initial_entry.first;

    const symbolt &symbol = ns.lookup(identifier);

    // wires do not have an initial value; their invariant
    // definition applies in the initial state
    if(!symbol.is_lvalue)
      continue;

    const symbol_exprt symbol_expr_raw{identifier, symbol.type};
    const auto lowered_type = verilog_lowering(symbol.type);

    // Slices that are not assigned are non-deterministic.
    exprt nondet = symbol_expr_raw;
    nondet.id(ID_nondet_symbol);
    nondet.set("initial_value", true);

    auto whole = whole_slice(symbol.type);

    auto value = compose_values(
      initial_entry.second,
      symbol_expr_raw,
      [&nondet, &whole](const verilog_rtl_slicet &fragment)
      { return extract_range(nondet, whole, fragment); });

    auto lowered_value =
      typecast_exprt::conditional_cast(lower(std::move(value)), lowered_type);

    // reads of state-holding variables yield their
    // non-deterministic pre-initial value
    initial_nondet(lowered_value);

    exprt lhs = symbol_expr(symbol, false);

    trans.init().add_to_operands(
      equal_exprt{std::move(lhs), std::move(lowered_value)});
  }

  // --initial-zero: default-initialize all state variables
  // that do not have an initial value
  if(initial_zero)
  {
    for(auto &identifier : rtl.variables)
    {
      const symbolt &symbol = ns.lookup(identifier);

      if(!symbol.is_lvalue)
        continue;

      if(rtl.initial_values.find(identifier) != rtl.initial_values.end())
        continue;

      auto initializer_opt = verilog_default_initializer(symbol.type);

      if(!initializer_opt.has_value())
        continue;

      exprt lhs = symbol_expr(symbol, false);

      trans.init().add_to_operands(equal_exprt{
        std::move(lhs),
        typecast_exprt::conditional_cast(
          lower(std::move(*initializer_opt)), verilog_lowering(symbol.type))});
    }
  }

  post_process_initial(trans.init());
}

/*******************************************************************\

Function: verilog_transition_relationt::convert_constraints

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_transition_relationt::convert_constraints(
  const verilog_rtlt &rtl,
  transt &trans)
{
  for(auto &constraint : rtl.constraints)
  {
    if(constraint.id() == "verilog-primitive-module")
    {
      // passed through as is
      trans.invar().add_to_operands(constraint);
    }
    else
    {
      auto lowered = lower(constraint);
      trans.invar().add_to_operands(
        typecast_exprt::conditional_cast(std::move(lowered), bool_typet{}));
    }
  }
}

/*******************************************************************\

Function: verilog_transition_relationt::set_default_sequence_semantics

  Inputs:

 Outputs:

 Purpose: 1800-2017 16.12.2 Sequence property

\*******************************************************************/

void verilog_transition_relationt::set_default_sequence_semantics(
  exprt &expr,
  bool strong)
{
  if(expr.id() == ID_sva_sequence_property)
  {
    // apply
    expr.id(strong ? ID_sva_implicit_strong : ID_sva_implicit_weak);
  }
  else if(expr.id() == ID_sva_not)
  {
    // flip
    set_default_sequence_semantics(to_sva_not_expr(expr).op(), !strong);
  }
  else
  {
    for(auto &op : expr.operands())
      set_default_sequence_semantics(op, strong);
  }
}

/*******************************************************************\

Function: verilog_transition_relationt::convert_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_transition_relationt::convert_properties(const verilog_rtlt &rtl)
{
  for(auto &property : rtl.properties)
  {
    symbolt &symbol = symbol_table.get_writeable_ref(property.identifier);

    using contextt = verilog_rtl_propertyt::contextt;

    // The comment shows the property in source-level form.
    {
      exprt cond_for_comment = property.source_condition;

      if(property.context != contextt::INITIAL && !property.is_cover())
      {
        // assertions and assumptions have an implicit 'always'
        if(cond_for_comment.id() != ID_sva_always)
          cond_for_comment = sva_always_exprt{cond_for_comment};
      }

      // Module-level assumptions are not marked in the comment.
      if(property.is_assume() && property.context != contextt::MODULE_LEVEL)
        cond_for_comment = sva_assume_exprt{cond_for_comment};
      else if(property.is_cover())
        cond_for_comment = sva_cover_exprt{cond_for_comment};

      symbol.location.set_comment(to_string(cond_for_comment));
    }

    auto cond = lower(property.condition);

    if(property.context != contextt::INITIAL && !property.is_cover())
    {
      // assertions and assumptions have an implicit 'always'
      if(cond.id() != ID_sva_always)
        cond = sva_always_exprt{cond};
    }

    if(property.is_assume())
    {
      cond = sva_assume_exprt{cond};
    }
    else if(property.is_cover())
    {
      if(property.is_sequence)
        cond = sva_cover_exprt{sva_sequence_property_exprt{cond}};
      else
        cond = sva_cover_exprt{cond};
    }

    // 1800-2017 16.12.2 Sequence property
    set_default_sequence_semantics(cond, property.is_cover());

    symbol.value = std::move(cond);
  }
}

/*******************************************************************\

Function: verilog_transition_relationt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

transt verilog_transition_relationt::convert()
{
  symbolt &module_symbol = symbol_table.get_writeable_ref(module);

  // done already?
  if(module_symbol.value.id() == ID_trans)
    return to_trans_expr(module_symbol.value);

  // construct the RTL representation, which includes
  // module instances recursively
  auto rtl = verilog_rtl(symbol_table, module, standard, message_handler);

  // Variables that are forced to a value, e.g. by a port
  // connection, become wires.
  for(auto &identifier : rtl.forced)
  {
    symbolt &symbol = symbol_table.get_writeable_ref(identifier);

    if(symbol.is_lvalue)
    {
      warning().source_location = symbol.location;
      warning() << "Making " << symbol.display_name() << " a wire" << eom;
      symbol.is_lvalue = false;
    }
  }

  transt trans{
    ID_trans,
    conjunction({}),
    conjunction({}),
    conjunction({}),
    module_symbol.type};

  convert_definitions(rtl, trans);
  convert_initial_values(rtl, trans);
  convert_constraints(rtl, trans);
  convert_properties(rtl);

  trans.invar() = conjunction(trans.invar().operands());
  trans.init() = conjunction(trans.init().operands());
  trans.trans() = conjunction(trans.trans().operands());

  module_symbol.value = trans;

  return trans;
}

/*******************************************************************\

Function: verilog_transition_relation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

transt verilog_transition_relation(
  symbol_table_baset &symbol_table,
  const irep_idt &module_identifier,
  verilog_standardt standard,
  bool ignore_initial,
  bool initial_zero,
  message_handlert &message_handler)
{
  const namespacet ns(symbol_table);

  verilog_transition_relationt converter(
    standard,
    symbol_table,
    ns,
    module_identifier,
    ignore_initial,
    initial_zero,
    message_handler);

  try
  {
    return converter.convert();
  }
  catch(verilog_transition_relationt::errort error)
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
