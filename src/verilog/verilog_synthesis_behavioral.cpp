/*******************************************************************\

Module: Verilog Synthesis (Behavioral)

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_synthesis_class.h"

#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/ebmc_util.h>
#include <util/expr_util.h>
#include <util/mathematical_types.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include <ebmc/ebmc_error.h>

#include "aval_bval_encoding.h"
#include "expr2verilog.h"
#include "verilog_expr.h"
#include "verilog_lowering.h"
#include "verilog_typecheck_expr.h"

#include <cassert>

/*******************************************************************\

Function: verilog_synthesist::function_locality

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::function_locality(const symbolt &function_symbol)
{
  // Find all local symbols of the function, mark their
  // assignments as local.
  auto prefix = id2string(function_symbol.name) + '.';
  for(auto &symbol : symbol_table.symbols)
  {
    if(symbol.first.starts_with(prefix))
    {
      assignments[symbol.first].is_cycle_local = true;
    }
  }
}

/*******************************************************************\

Function: verilog_synthesist::expand_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_synthesist::expand_function_call(
  const function_call_exprt &call,
  symbol_statet symbol_state)
{
  // Is it a 'system function call'?
  if(call.is_system_function_call())
  {
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
      auto what = synth_expr_rec(call.arguments()[0], symbol_state);
      auto ticks = call.arguments().size() < 2
                     ? from_integer(1, integer_typet())
                     : call.arguments()[1];
      return verilog_past_exprt{what, ticks}.with_source_location(call);
    }
    else if(
      base_name == "$stable" || base_name == "$rose" || base_name == "$fell" ||
      base_name == "$changed")
    {
      DATA_INVARIANT(call.arguments().size() >= 1, "must have argument");
      auto what = synth_expr_rec(call.arguments()[0], symbol_state);
      auto past = verilog_past_exprt{what, from_integer(1, integer_typet())}
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
      else if(base_name == "$fell")
        return and_exprt{lsb(past), not_exprt{lsb(what)}};
      else
        DATA_INVARIANT(false, "all cases covered");
    }
    else if(base_name == "$countones")
    {
      // lower to popcount
      DATA_INVARIANT(
        call.arguments().size() == 1, "$countones must have one argument");
      auto what = synth_expr(call.arguments()[0], symbol_state); // rec. call
      return popcount_exprt{what, call.type()};
    }
    else
    {
      // Attempt to constant fold.
      verilog_typecheck_exprt verilog_typecheck_expr(
        standard, false, ns, get_message_handler());
      auto result =
        verilog_typecheck_expr.elaborate_constant_system_function_call(call);
      if(!result.is_constant())
      {
        throw errort().with_location(call.source_location())
          << "cannot synthesise system function " << to_string(call.function());
      }

      return result;
    }
  }

  // check some restrictions
  if(construct == constructt::OTHER)
  {
    throw errort().with_location(call.source_location())
      << "function call not allowed here";
  }

  // this is essentially inlined
  const symbol_exprt &function = to_symbol_expr(call.function());

  const symbolt &symbol = ns.lookup(function);

  if(symbol.type.id() != ID_code)
  {
    throw errort().with_location(call.source_location())
      << "function call expects function argument";
  }

  const code_typet &code_type = to_code_type(symbol.type);

  if(code_type.return_type() == empty_typet())
  {
    throw errort().with_location(call.source_location())
      << "function call cannot call task";
  }

  // preserve the previous call frame, if any
  auto old_tf_frame = tf_frame;

  // remember the guard
  auto entry_guard = value_map->guard;

  // create a fresh call frame
  tf_frame = tf_framet{};

  const symbolt &return_symbol =
    ns.lookup(id2string(symbol.name) + "." + id2string(symbol.base_name));

  tf_frame.value().return_value = return_symbol.symbol_expr();

  const code_typet::parameterst &parameters = code_type.parameters();

  const exprt::operandst &actuals = call.op1().operands();

  if(parameters.size() != actuals.size())
  {
    throw errort().with_location(call.source_location())
      << "wrong number of arguments";
  }

  // preserve locality of function-local variables
  function_locality(symbol);

  // do assignments to function parameters
  for(unsigned i = 0; i < parameters.size(); i++)
  {
    const symbolt &a_symbol = ns.lookup(parameters[i].get_identifier());
    verilog_blocking_assignt assignment{
      a_symbol.symbol_expr().with_source_location(call), actuals[i]};
    assignment.add_source_location() = call.source_location();
    synth_statement(assignment);
  }

  for(auto &statement : symbol.value.operands())
    synth_statement(to_verilog_statement(statement));

  // merge in edges from 'return' statements, if any
  for(auto &state : tf_frame.value().return_statement_states)
  {
    auto guard_expr = conjunction(state.guard);
    merge(
      guard_expr, state.current, value_map->current, false, value_map->current);
    merge(guard_expr, state.final, value_map->final, true, value_map->final);
  }

  // replace function call by return value symbol
  auto result = synth_expr(return_symbol.symbol_expr(), symbol_statet::CURRENT);

  // restore the previous task/function frame
  tf_frame = old_tf_frame;
  value_map->guard = entry_guard;

  // do assignments to output parameters
  for(unsigned i = 0; i < parameters.size(); i++)
  {
    const symbolt &a_symbol = ns.lookup(parameters[i].get_identifier());
    if(parameters[i].get_bool(ID_output))
    {
      verilog_blocking_assignt assignment{actuals[i], a_symbol.symbol_expr()};
      assignment.add_source_location() = call.source_location();
      synth_statement(assignment);
    }
  }

  return result;
}

/*******************************************************************\

Function: verilog_synthesist::assignment_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::assignment_rec(
  const exprt &lhs, // synth_lhs_expr applied
  const exprt &rhs, // synth_expr applied
  bool blocking)
{
  if(lhs.id() == ID_concatenation) // split it up
  {
    // TODO: split it up more intelligently;
    // bit-wise is wasteful.
    mp_integer offset = 0;

    // do it from right to left

    for(exprt::operandst::const_reverse_iterator it = lhs.operands().rbegin();
        it != lhs.operands().rend();
        it++)
    {
      auto offset_constant = from_integer(offset, natural_typet{});

      if(it->type().id() == ID_bool)
      {
        exprt bit_extract = extractbit_exprt{rhs, offset_constant};
        ++offset;

        assignment_rec(*it, bit_extract, blocking);
      }
      else if(
        it->type().id() == ID_signedbv || it->type().id() == ID_unsignedbv)
      {
        extractbits_exprt bit_extract(rhs, offset_constant, it->type());

        assignment_rec(*it, bit_extract, blocking);

        auto width = get_width(it->type());
        offset += width;
      }
      else
      {
        throw errort().with_location(it->source_location())
          << "assignment to type `" << to_string(it->type())
          << "' not supported";
      }
    }

    return;
  }

  // get identifier
  const symbolt &symbol = assignment_symbol(lhs);

  if(symbol.type.id() == ID_verilog_realtime)
  {
    // we silently ignore these
    return;
  }

  if(!symbol.is_lvalue)
  {
    throw errort().with_location(lhs.source_location())
      << "assignment to non-variable";
  }

  if(construct == constructt::ALWAYS && event_guard == event_guardt::NONE)
  {
    throw errort().with_location(lhs.source_location())
      << "assignment in 'always' context without event guard";
  }

  if(construct == constructt::ALWAYS_FF && event_guard == event_guardt::NONE)
  {
    throw errort().with_location(lhs.source_location())
      << "assignment in 'always_ff' context without event guard";
  }

  {
    event_guardt new_type;

    if(construct == constructt::INITIAL)
      new_type = event_guardt::CLOCK;
    else if(construct == constructt::ALWAYS_COMB)
      new_type = event_guardt::COMBINATIONAL;
    else
      new_type = event_guard;

    assignmentt &assignment = assignments[symbol.name];

    if(assignment.is_cycle_local)
    {
    }
    else
    {
      if(assignment.type == event_guardt::NONE)
        assignment.type = new_type;
      else if(assignment.type != new_type)
      {
        throw errort().with_location(lhs.source_location())
          << "conflicting assignment types for `" << symbol.base_name
          << "' (new: " << as_string(new_type)
          << ", old: " << as_string(assignment.type) << ")";
      }

      membert member;
      assignment_member_rec(
        lhs,
        member,
        (construct == constructt::INITIAL) ? assignment.init : assignment.next);
    }
  }

  {
    assert(value_map != NULL);

    auto new_value = assignment_rec(lhs, rhs); // start of recursion

    if(new_value.is_not_nil())
    {
      // These can explode if the symbol is assigned more than once
      // and also used more than once, e.g., in a multi-dimensional array.
      // We add a fresh symbol for anything that is not trivial
      // to prevent that.
      if(new_value.id() != ID_symbol && new_value.id() != ID_constant)
      {
        replace_by_wire(new_value, symbol);
      }

      if(blocking)
        value_map->current.assign(symbol.name, new_value);

      value_map->final.assign(symbol.name, new_value);
    }
  }
}

/*******************************************************************\

Function: verilog_synthesist::assignment_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_synthesist::assignment_rec(
  const exprt &lhs, // synth_lhs_expr applied
  const exprt &rhs) // synth_expr applied
{
  if(lhs.id() == ID_symbol)
  {
    return rhs;
  }
  else if(lhs.id() == ID_index || lhs.id() == ID_extractbit)
  {
    if(lhs.operands().size() != 2)
    {
      throw errort() << "index takes two operands";
    }

    const exprt &lhs_array = to_binary_expr(lhs).op0();
    const exprt &lhs_index = to_binary_expr(lhs).op1();

    // turn
    //   a[i]=e
    // into
    //   a'==a WITH [i:=e]

    with_exprt new_rhs(lhs_array, lhs_index, rhs);

    // do the array
    new_rhs.old() = synth_expr(new_rhs.old(), symbol_statet::FINAL);

    return assignment_rec(lhs_array, new_rhs); // recursive call
  }
  else if(lhs.id() == ID_verilog_non_indexed_part_select)
  {
    // we flatten n-bit part select into n times extractbit
    auto &part_select = to_verilog_non_indexed_part_select_expr(lhs);

    const exprt &lhs_src = part_select.src();
    const exprt &lhs_msb = part_select.msb();
    const exprt &lhs_lsb = part_select.lsb();

    mp_integer from, to;

    if(to_integer_non_constant(lhs_msb, to))
    {
      throw errort().with_location(lhs_msb.source_location())
        << "failed to convert range";
    }

    if(to_integer_non_constant(lhs_lsb, from))
    {
      throw errort().with_location(lhs_lsb.source_location())
        << "failed to convert range";
    }

    if(from > to)
      std::swap(from, to);

    // redundant?
    if(from == 0 && to == get_width(lhs_src.type()) - 1)
    {
      return assignment_rec(lhs_src, rhs); // recursive call
    }

    // turn
    //   a[i]=e
    // into
    //   a'==a WITH [from:=e[0]] ... WITH [to:=e[to-from]]

    // synthesise 'a'
    auto new_rhs = synth_expr(lhs_src, symbol_statet::FINAL);
    const auto rhs_width = get_width(lhs_src.type());

    // We drop bits that are out of bounds
    auto from_in_range = std::max(mp_integer{0}, from);
    auto to_in_range = std::min(rhs_width - 1, to);

    // add the WITH expressions for the indexes in the range
    for(mp_integer i = from_in_range; i <= to_in_range; ++i)
    {
      exprt offset = from_integer(i - from, integer_typet{});
      exprt rhs_extractbit = extractbit_exprt{rhs, std::move(offset)};
      exprt count = from_integer(i, integer_typet{});
      new_rhs = with_exprt{
        std::move(new_rhs), std::move(count), std::move(rhs_extractbit)};
    }

    return assignment_rec(lhs_src, new_rhs); // recrusive call
  }
  else if(
    lhs.id() == ID_verilog_indexed_part_select_plus ||
    lhs.id() == ID_verilog_indexed_part_select_minus)
  {
    // we flatten n-bit part select into n times extractbit
    auto &part_select = to_verilog_indexed_part_select_plus_or_minus_expr(lhs);

    const exprt &lhs_src = part_select.src();
    const exprt &lhs_index = part_select.index();
    const exprt &lhs_width = part_select.width();

    auto index_opt = synthesis_constant(lhs_index);

    if(!index_opt.has_value())
    {
      throw errort().with_location(lhs_index.source_location())
        << "failed to convert part select index";
    }

    auto width_opt = synthesis_constant(lhs_width);

    if(!width_opt.has_value())
    {
      throw errort().with_location(lhs_width.source_location())
        << "failed to convert part select width";
    }

    mp_integer index = *index_opt, width = *width_opt;

    // turn
    //   a[i +: w]=e  (selects bits i to i+w-1)
    //   a[i -: w]=e  (selects bits i-w+1 to i)
    // into
    //   a'==a WITH [lo:=e[0]] ... WITH [lo+w-1:=e[w-1]]

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

    // start with 'a'
    auto new_rhs = synth_expr(lhs_src, symbol_statet::FINAL);
    const auto rhs_width = get_width(lhs_src.type());

    // We drop bits that are out of bounds
    auto from_in_range = std::max(mp_integer{0}, lo);
    auto to_in_range = std::min(rhs_width - 1, hi);

    // now add the indexes in the range
    for(mp_integer i = from_in_range; i <= to_in_range; ++i)
    {
      exprt offset = from_integer(i - lo, integer_typet{});
      exprt rhs_extractbit = extractbit_exprt{rhs, std::move(offset)};
      exprt count = from_integer(i, integer_typet{});
      new_rhs = with_exprt{
        std::move(new_rhs), std::move(count), std::move(rhs_extractbit)};
    }

    return assignment_rec(lhs_src, new_rhs); // recursive call
  }
  else if(lhs.id() == ID_member)
  {
    const auto &member_expr = to_member_expr(lhs);
    const exprt &lhs_compound = member_expr.struct_op();
    auto component_name = member_expr.get_component_name();

    if(
      lhs_compound.type().id() == ID_struct ||
      lhs_compound.type().id() == ID_union)
    {
      // turn
      //   s.m=e
      // into
      //   s'==s WITH [m:=e]
      auto synth_compound = synth_expr(lhs_compound, symbol_statet::FINAL);

      with_exprt new_rhs{
        synth_compound, member_designatort{component_name}, rhs};

      // recursive call
      return assignment_rec(lhs_compound, new_rhs); // recursive call
    }
    else
    {
      throw errort() << "unexpected member lhs: " << lhs_compound.type().id();
    }
  }
  else if(lhs.id() == ID_typecast)
  {
    // The cast is assumed to be a reinterpret cast.
    // (T)lhs = rhs
    auto &typecast_expr = to_typecast_expr(lhs);

    // note that the LHS is not yet fully synthesised; we will need to lower
    // the typecast
    auto new_rhs = typecast_exprt{rhs, typecast_expr.op().type()};

    auto new_rhs_lowered = verilog_lowering_cast(new_rhs);

    return assignment_rec(typecast_expr.op(), new_rhs_lowered);
  }
  else
  {
    throw errort() << "unexpected lhs: " << lhs.id();
  }
}

/*******************************************************************\

Function: verilog_synthesist::synth_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_block(const verilog_blockt &statement)
{
  for(auto &block_statement : statement.statements())
    synth_statement(block_statement);
}

/*******************************************************************\

Function: verilog_synthesist::synth_break

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_break(const verilog_breakt &statement)
{
  PRECONDITION(loop_frame.has_value());

  loop_frame.value().break_statement_states.push_back(*value_map);

  // set guard to false
  value_map->guard.push_back(false_exprt{});
}

/*******************************************************************\

Function: verilog_synthesist::synth_continue

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_continue(const verilog_continuet &statement)
{
  PRECONDITION(loop_frame.has_value());

  loop_frame.value().continue_statement_states.push_back(*value_map);

  // set guard to false
  value_map->guard.push_back(false_exprt{});
}

/*******************************************************************\

Function: verilog_synthesist::synth_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_assign(const verilog_assignt &statement)
{
  if(construct == constructt::OTHER)
  {
    throw errort().with_location(statement.source_location())
      << "unexpected assignment statement";
  }

  exprt lhs = statement.lhs();
  lhs = synth_lhs_expr(lhs);

  exprt rhs = statement.rhs();
  rhs = synth_expr(rhs, symbol_statet::CURRENT);

  irep_idt compound_id = irep_idt{};

  if(statement.id() == ID_verilog_blocking_assign_plus)
    compound_id = ID_plus;
  else if(statement.id() == ID_verilog_blocking_assign_minus)
    compound_id = ID_minus;
  else if(statement.id() == ID_verilog_blocking_assign_mult)
    compound_id = ID_mult;
  else if(statement.id() == ID_verilog_blocking_assign_div)
    compound_id = ID_div;
  else if(statement.id() == ID_verilog_blocking_assign_mod)
    compound_id = ID_mod;
  else if(statement.id() == ID_verilog_blocking_assign_bitand)
    compound_id = ID_bitand;
  else if(statement.id() == ID_verilog_blocking_assign_bitor)
    compound_id = ID_bitor;
  else if(statement.id() == ID_verilog_blocking_assign_bitxor)
    compound_id = ID_bitxor;
  else if(statement.id() == ID_verilog_blocking_assign_lshr)
    compound_id = ID_lshr;
  else if(statement.id() == ID_verilog_blocking_assign_lshl)
    compound_id = ID_shl;
  else if(statement.id() == ID_verilog_blocking_assign_ashr)
    compound_id = ID_ashr;
  else if(statement.id() == ID_verilog_blocking_assign_ashl)
    compound_id = ID_shl;

  if(compound_id != irep_idt{})
  {
    auto lhs_synth = synth_expr(lhs, symbol_statet::CURRENT);
    rhs = binary_exprt{std::move(lhs_synth), compound_id, rhs, rhs.type()};
  }

  // Can the rhs be simplified to a constant, for propagation?
  auto rhs_simplified = simplify_expr(rhs, ns);

  if(rhs_simplified.is_constant())
    rhs = rhs_simplified;

  bool blocking = statement.id() != ID_verilog_non_blocking_assign;

  assignment_rec(lhs, rhs, blocking);
}

/*******************************************************************\

Function: verilog_synthesist::case_comparison

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_synthesist::case_comparison(
  const exprt &case_operand,
  const exprt &pattern)
{
  // the pattern has the max type, not the case operand
  const typet &pattern_type = pattern.type();

  // we need to take case of ?, x, z in the pattern
  if(is_aval_bval(pattern_type))
  {
    // We are using masking based on the pattern.
    // The aval is the comparison value, and the
    // negation of bval is the mask.
    auto pattern_aval = ::aval(pattern);
    auto pattern_bval = ::bval(pattern);
    auto mask_expr = bitnot_exprt{pattern_bval};

    auto case_operand_casted = typecast_exprt{
      typecast_exprt::conditional_cast(
        case_operand, aval_bval_underlying(pattern_type)),
      mask_expr.type()};

    return equal_exprt{
      bitand_exprt{case_operand_casted, mask_expr},
      bitand_exprt{pattern_aval, mask_expr}};
  }

  // 2-valued comparison
  exprt case_operand_casted =
    typecast_exprt::conditional_cast(case_operand, pattern_type);

  return equal_exprt(case_operand_casted, pattern);
}

/*******************************************************************\

Function: verilog_synthesist::synth_case_values

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_synthesist::synth_case_values(
  const exprt &values,
  const exprt &case_operand)
{
  if(values.id() == ID_default)
    return true_exprt();

  exprt::operandst op;

  op.reserve(values.operands().size());

  forall_operands(it, values)
  {
    auto pattern = synth_expr(*it, symbol_statet::CURRENT);
    op.push_back(case_comparison(case_operand, pattern));
  }

  return disjunction(op);
}

/*******************************************************************\

Function: verilog_synthesist::synth_case

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_case(
  const verilog_case_statement_baset &statement)
{
  if(statement.operands().size() < 1)
  {
    throw errort().with_location(statement.source_location())
      << "case statement expected to have at least one operand";
  }

  // do the argument of the case
  auto case_operand =
    synth_expr(statement.case_operand(), symbol_statet::CURRENT);

  // we convert the rest to if-then-else
  exprt start;
  exprt *last_if = &start;
  std::optional<verilog_statementt> default_case;

  for(unsigned i = 1; i < statement.operands().size(); i++)
  {
    const exprt &e = statement.operands()[i];

    if(e.id() != ID_case_item)
    {
      throw errort() << "expected case_item";
    }

    auto &case_item = to_verilog_case_item(e);

    // default?
    if(case_item.is_default())
      default_case = case_item.case_statement();
    else
    {
      exprt if_statement(ID_if);
      if_statement.reserve_operands(3);
      if_statement.add_to_operands(
        synth_case_values(case_item.case_value(), case_operand));
      if_statement.add_to_operands(case_item.case_statement());

      last_if->add_to_operands(std::move(if_statement));
      last_if = &last_if->operands().back();
    }
  }

  if(default_case.has_value())
  {
    // Attach the 'default' to the final 'if' as 'else'
    last_if->add_to_operands(std::move(default_case.value()));
  }

  // synthesize the new if-then-else

  if(!start.operands().empty())
    synth_statement(
      static_cast<verilog_statementt &>(to_multi_ary_expr(start).op0()));
}

/*******************************************************************\

Function: verilog_synthesist::synth_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_if(const verilog_ift &statement)
{
  auto if_cond = synth_expr(statement.cond(), symbol_statet::CURRENT);

  if(if_cond.is_true())
  {
    synth_statement(statement.then_case());
    return;
  }

  // save current value_map pointer
  value_mapt *old_map = value_map;

  // produce new value maps
  value_mapt true_map(*value_map), false_map(*value_map);

  true_map.clear_changed();
  true_map.guard.push_back(if_cond);

  false_map.clear_changed();
  false_map.guard.push_back(not_exprt{if_cond});

  // 'then' case
  {
    value_map = &true_map;
    synth_statement(statement.then_case());
  }

  // 'else' case
  if(statement.has_else_case())
  {
    value_map = &false_map;
    synth_statement(statement.else_case());
  }

  // restore and merge
  value_map = old_map;

  // merge current map
  merge(
    if_cond, true_map.current, false_map.current, false, value_map->current);

  // merge final map
  merge(if_cond, true_map.final, false_map.final, true, value_map->final);
}

/*******************************************************************\

Function: verilog_synthesist::merge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::merge(
  const exprt &guard,
  const value_mapt::mapt &true_map,
  const value_mapt::mapt &false_map,
  bool use_previous_assignments,
  value_mapt::mapt &dest)
{
  // get true_map.changed + false_map.changed

  std::set<irep_idt> changed;

  changed.insert(true_map.changed.begin(), true_map.changed.end());
  changed.insert(false_map.changed.begin(), false_map.changed.end());

  for(const auto &it : changed)
  {
    const symbolt &symbol = ns.lookup(it);

    exprt true_value =
      current_value(true_map, symbol, use_previous_assignments);
    exprt false_value =
      current_value(false_map, symbol, use_previous_assignments);

    // this is a phi-node equivalent
    if_exprt value{guard, true_value, false_value, symbol.type};

    dest.symbol_map[symbol.name].swap(value);
    dest.changed.insert(symbol.name);
  }
}

/*******************************************************************\

Function: verilog_synthesist::synth_event_guard

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_event_guard(
  const verilog_event_guardt &statement)
{
  if(statement.operands().size() != 2)
  {
    throw errort().with_location(statement.source_location())
      << "event_guard expected to have two operands";
  }

  if(event_guard != event_guardt::NONE)
  {
    throw errort().with_location(statement.source_location())
      << "event guard already specified";
  }

  const exprt &event_guard_expr = statement.guard();

  bool edge = false;

  // these guards are ORed
  exprt::operandst guards;

  forall_operands(it, event_guard_expr)
    if(it->id() == ID_posedge || it->id() == ID_negedge)
    {
      edge = true;

      if(it->operands().size() != 1)
      {
        throw errort().with_location(it->source_location())
          << "pos/negedge expected to have one operand";
      }

      irep_idt identifier = "conf::clock_enable_mode";

      // check symbol_table for clock guard

      if(symbol_table.symbols.find(identifier) != symbol_table.symbols.end())
      {
        // found! we make it a guard

        auto &op = to_unary_expr(*it).op();

        if(op.type().id() == ID_bool)
          guards.push_back(op);
        else
        {
          // get LSB
          guards.push_back(extractbit_exprt{op, integer_typet{}.zero_expr()});
        }

        throw errort() << "Notice: using clock guard " << identifier;
      }
    }

  event_guard = edge ? event_guardt::CLOCK : event_guardt::COMBINATIONAL;

  if(guards.empty())
    synth_statement(statement.body());
  else
  {
    // new guards!
    exprt guard_expr = disjunction(guards);

    value_mapt *old_map = value_map;
    value_mapt true_map(*value_map), false_map(*value_map);
    true_map.clear_changed();
    false_map.clear_changed();

    value_map = &true_map;
    synth_statement(statement.body());

    value_map = old_map;
    merge(
      guard_expr,
      true_map.current,
      false_map.current,
      false,
      value_map->current);
    merge(guard_expr, true_map.final, false_map.final, true, value_map->final);
  }

  event_guard = event_guardt::NONE;
}

/*******************************************************************\

Function: verilog_synthesist::synth_delay

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_delay(const verilog_delayt &statement)
{
  if(statement.operands().size() != 2)
  {
    throw errort().with_location(statement.source_location())
      << "delay expected to have two operands";
  }

  synth_statement(statement.body());
}

/*******************************************************************\

Function: verilog_synthesist::synth_for

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_for(const verilog_fort &statement)
{
  if(statement.operands().size() != 4)
  {
    throw errort().with_location(statement.source_location())
      << "for expected to have four operands";
  }

  auto old_loop_frame = std::move(loop_frame);
  loop_frame = loop_framet{};

  for(auto &init : statement.initialization())
  {
    // either an assignment or a declaration with assignment
    if(
      init.id() == ID_verilog_blocking_assign ||
      init.id() == ID_verilog_non_blocking_assign)
    {
      synth_statement(init);
    }
    else if(init.id() == ID_decl)
    {
      // turn into a blocking assignment
      auto &decl = to_verilog_decl(init);
      for(auto &declarator : decl.declarators())
      {
        DATA_INVARIANT(
          declarator.value().is_not_nil(),
          "for-init declarator must have value");
        auto assignment = verilog_blocking_assignt{
          declarator.symbol_expr(), declarator.value()};
        synth_assign(assignment);
      }
    }
    else
    {
      DATA_INVARIANT_WITH_DIAGNOSTICS(
        false, "unexpected initialization in for loop", init.pretty());
    }
  }

  while(true)
  {
    loop_frame.value().continue_statement_states.clear();

    DATA_INVARIANT(
      statement.condition().type().id() == ID_bool,
      "for condition must be Boolean");

    auto guard_value_opt = synthesis_constant(statement.condition());

    if(!guard_value_opt.has_value())
    {
      throw errort().with_location(statement.condition().source_location())
        << "synthesis failed to evaluate loop guard: `"
        << to_string(statement.condition()) << '\'';
    }

    if(guard_value_opt.value() == 0)
      break;

    // execute the body
    synth_statement(statement.body());

    // merge in edges from 'continue' statements, if any
    for(auto &state : loop_frame.value().continue_statement_states)
    {
      auto guard_expr = conjunction(state.guard);
      merge(
        guard_expr,
        state.current,
        value_map->current,
        false,
        value_map->current);
      merge(guard_expr, state.final, value_map->final, true, value_map->final);
    }

    // execute the step statement
    synth_statement(statement.inc_statement());
  }

  // Merge in edges from 'break' statements, if any. These come
  // in program order, hence process in reverse order.
  auto &break_states = loop_frame.value().break_statement_states;

  for(auto state_it = break_states.rbegin(); state_it != break_states.rend();
      ++state_it)
  {
    auto &state = *state_it;
    auto guard_expr = conjunction(state.guard);
    merge(
      guard_expr, state.current, value_map->current, false, value_map->current);
    merge(guard_expr, state.final, value_map->final, true, value_map->final);
  }

  loop_frame = std::move(old_loop_frame);
}

/*******************************************************************\

Function: verilog_synthesist::synth_prepostincdec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_prepostincdec(
  const verilog_statementt &statement)
{
  if(statement.operands().size() != 1)
  {
    throw errort().with_location(statement.source_location())
      << statement.id() << " expected to have one operand";
  }

  const auto &op = to_unary_expr(statement).op();

  // stupid implementation
  exprt one = from_integer(1, op.type());

  bool increment =
    statement.id() == ID_preincrement || statement.id() == ID_postincrement;

  exprt rhs;

  if(increment)
    rhs = plus_exprt(op, one);
  else
    rhs = minus_exprt(op, one);

  verilog_blocking_assignt assignment{op, rhs};
  assignment.add_source_location() = statement.source_location();

  synth_statement(assignment);
}

/*******************************************************************\

Function: verilog_synthesist::synth_while

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_while(const verilog_whilet &statement)
{
  if(statement.operands().size() != 2)
  {
    throw errort().with_location(statement.source_location())
      << "while expected to have two operands";
  }

  auto old_loop_frame = std::move(loop_frame);
  loop_frame = loop_framet{};

  while(true)
  {
    loop_frame.value().continue_statement_states.clear();

    exprt tmp_guard = statement.condition();
    tmp_guard = typecast_exprt{tmp_guard, bool_typet{}};
    tmp_guard = synth_expr(tmp_guard, symbol_statet::CURRENT);
    simplify(tmp_guard, ns);

    if(!tmp_guard.is_constant())
    {
      throw errort().with_location(statement.body().source_location())
        << "synthesis failed to evaluate loop guard: `" << to_string(tmp_guard)
        << '\'';
    }

    if(tmp_guard.is_false())
      break;

    // execute the body
    synth_statement(statement.body());

    // merge in edges from 'continue' statements, if any
    for(auto &state : loop_frame.value().continue_statement_states)
    {
      auto guard_expr = conjunction(state.guard);
      merge(
        guard_expr,
        state.current,
        value_map->current,
        false,
        value_map->current);
      merge(guard_expr, state.final, value_map->final, true, value_map->final);
    }
  }

  // Merge in edges from 'break' statements, if any. These come
  // in program order, hence process in reverse order.
  auto &break_states = loop_frame.value().break_statement_states;

  for(auto state_it = break_states.rbegin(); state_it != break_states.rend();
      ++state_it)
  {
    auto &state = *state_it;
    auto guard_expr = conjunction(state.guard);
    merge(
      guard_expr, state.current, value_map->current, false, value_map->current);
    merge(guard_expr, state.final, value_map->final, true, value_map->final);
  }

  loop_frame = std::move(old_loop_frame);
}

/*******************************************************************\

Function: verilog_synthesist::synth_repeat

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_repeat(const verilog_repeatt &statement)
{
  if(statement.operands().size() != 2)
  {
    throw errort().with_location(statement.source_location())
      << "repeat expected to have two operands";
  }

  throw errort().with_location(statement.source_location())
    << "cannot synthesize `repeat'";
}

/*******************************************************************\

Function: verilog_synthesist::synth_return

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_return(const verilog_returnt &statement)
{
  // There has to be a tf frame
  PRECONDITION(tf_frame.has_value());

  auto &frame = tf_frame.value();

  // return value?
  if(statement.has_value())
  {
    // assign to the symbol with the function's name
    DATA_INVARIANT(
      frame.return_value.has_value(),
      "return with value requires return value symbol");

    verilog_assignt assignment{
      ID_verilog_blocking_assign,
      frame.return_value.value(),
      statement.value()};

    synth_assign(assignment);
  }

  frame.return_statement_states.push_back(*value_map);

  // set guard to false
  value_map->guard.push_back(false_exprt{});
}

/*******************************************************************\

Function: verilog_synthesist::synth_forever

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_forever(const verilog_forevert &statement)
{
  if(statement.operands().size() != 1)
  {
    throw errort().with_location(statement.source_location())
      << "forever expected to have one operand";
  }

  throw errort().with_location(statement.source_location())
    << "cannot synthesize `forever'";
}

/*******************************************************************\

Function: verilog_synthesist::synth_function_call_or_task_enable

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_function_call_or_task_enable(
  const verilog_function_callt &statement)
{
  if(statement.is_system_function_call())
  {
    // ignore system functions
  }
  else
  {
    // this is essentially inlined
    const symbol_exprt &function = to_symbol_expr(statement.function());
    const symbolt &symbol = ns.lookup(function);

    if(symbol.type.id() != ID_code)
    {
      throw errort().with_location(statement.source_location())
        << "expected function or task as first operand";
    }

    const code_typet &code_type = to_code_type(symbol.type);

    // preserve the previous call frame, if any
    auto old_tf_frame = tf_frame;

    // remember the guard
    auto entry_guard = value_map->guard;

    // create a fresh call frame
    tf_frame = tf_framet{};

    const code_typet::parameterst &parameters = code_type.parameters();

    const exprt::operandst &actuals = statement.arguments();

    if(parameters.size() != actuals.size())
    {
      throw errort().with_location(statement.source_location())
        << "wrong number of arguments";
    }

    // do assignments to input parameters
    for(unsigned i = 0; i < parameters.size(); i++)
    {
      const symbolt &a_symbol = ns.lookup(parameters[i].get_identifier());
      if(parameters[i].get_bool(ID_input))
      {
        verilog_blocking_assignt assignment{a_symbol.symbol_expr(), actuals[i]};
        assignment.add_source_location() = statement.source_location();
        synth_statement(assignment);
      }
    }

    for(auto &statement : symbol.value.operands())
      synth_statement(to_verilog_statement(statement));

    // merge in edges from 'return' statements, if any
    for(auto &state : tf_frame.value().return_statement_states)
    {
      auto guard_expr = conjunction(state.guard);
      merge(
        guard_expr,
        state.current,
        value_map->current,
        false,
        value_map->current);
      merge(guard_expr, state.final, value_map->final, true, value_map->final);
    }

    // restore the previous task/function frame
    tf_frame = old_tf_frame;
    value_map->guard = entry_guard;

    // do assignments to output parameters
    for(unsigned i = 0; i < parameters.size(); i++)
    {
      const symbolt &a_symbol = ns.lookup(parameters[i].get_identifier());
      if(parameters[i].get_bool(ID_output))
      {
        verilog_blocking_assignt assignment{actuals[i], a_symbol.symbol_expr()};
        assignment.add_source_location() = statement.source_location();
        synth_statement(assignment);
      }
    }
  }
}

/*******************************************************************\

Function: verilog_synthesist::synth_statement

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_synthesist::synth_statement(const verilog_statementt &statement)
{
  if(statement.id() == ID_block)
    synth_block(to_verilog_block(statement));
  else if(statement.id() == ID_break)
    synth_break(to_verilog_break(statement));
  else if(
    statement.id() == ID_verilog_case || statement.id() == ID_verilog_casex ||
    statement.id() == ID_verilog_casez)
  {
    synth_case(to_verilog_case_statement_base(statement));
  }
  else if(
    statement.id() == ID_verilog_blocking_assign ||
    statement.id() == ID_verilog_blocking_assign_plus ||
    statement.id() == ID_verilog_blocking_assign_minus ||
    statement.id() == ID_verilog_blocking_assign_mult ||
    statement.id() == ID_verilog_blocking_assign_div ||
    statement.id() == ID_verilog_blocking_assign_mod ||
    statement.id() == ID_verilog_blocking_assign_bitand ||
    statement.id() == ID_verilog_blocking_assign_bitor ||
    statement.id() == ID_verilog_blocking_assign_bitxor ||
    statement.id() == ID_verilog_blocking_assign_lshr ||
    statement.id() == ID_verilog_blocking_assign_lshl ||
    statement.id() == ID_verilog_blocking_assign_ashr ||
    statement.id() == ID_verilog_blocking_assign_ashl)
  {
    synth_assign(to_verilog_assign(statement));
  }
  else if(statement.id() == ID_continue)
    synth_continue(to_verilog_continue(statement));
  else if(statement.id() == ID_procedural_continuous_assign)
  {
    throw errort().with_location(statement.source_location())
      << "synthesis of procedural continuous assignment not supported";
  }
  else if(
    statement.id() == ID_verilog_immediate_assert ||
    statement.id() == ID_verilog_assert_property ||
    statement.id() == ID_verilog_smv_assert ||
    statement.id() == ID_verilog_immediate_cover ||
    statement.id() == ID_verilog_cover_property ||
    statement.id() == ID_verilog_cover_sequence)
  {
    synth_assert_assume_cover(
      to_verilog_assert_assume_cover_statement(statement));
  }
  else if(
    statement.id() == ID_verilog_immediate_assume ||
    statement.id() == ID_verilog_assume_property ||
    statement.id() == ID_verilog_restrict_property ||
    statement.id() == ID_verilog_smv_assume)
  {
    synth_assert_assume_cover(
      to_verilog_assert_assume_cover_statement(statement));
  }
  else if(statement.id() == ID_verilog_expect_property)
  {
    throw errort().with_location(statement.source_location())
      << "synthesis of expect property not supported";
  }
  else if(statement.id() == ID_verilog_non_blocking_assign)
    synth_assign(to_verilog_assign(statement));
  else if(statement.id() == ID_force)
    synth_force(to_verilog_force(statement));
  else if(statement.id() == ID_if)
    synth_if(to_verilog_if(statement));
  else if(statement.id() == ID_event_guard)
    synth_event_guard(to_verilog_event_guard(statement));
  else if(statement.id() == ID_delay)
    synth_delay(to_verilog_delay(statement));
  else if(statement.id() == ID_for)
    synth_for(to_verilog_for(statement));
  else if(statement.id() == ID_while)
    synth_while(to_verilog_while(statement));
  else if(statement.id() == ID_repeat)
    synth_repeat(to_verilog_repeat(statement));
  else if(statement.id() == ID_return)
    synth_return(to_verilog_return(statement));
  else if(statement.id() == ID_forever)
    synth_forever(to_verilog_forever(statement));
  else if(statement.id() == ID_function_call)
    synth_function_call_or_task_enable(to_verilog_function_call(statement));
  else if(
    statement.id() == ID_preincrement || statement.id() == ID_predecrement ||
    statement.id() == ID_postincrement || statement.id() == ID_postdecrement)
    synth_prepostincdec(statement);
  else if(statement.id() == ID_decl)
  {
    auto decl_class = to_verilog_decl(statement).get_class();

    if(decl_class == ID_function || decl_class == ID_task)
    {
    }
    else
      synth_decl(to_verilog_decl(statement));
  }
  else if(statement.id() == ID_skip)
  {
    // do nothing
  }
  else if(statement.id() == ID_verilog_label_statement)
    synth_statement(to_verilog_label_statement(statement).statement());
  else if(statement.id() == ID_verilog_event_trigger)
  {
    // not synthesized
  }
  else
  {
    throw errort().with_location(statement.source_location())
      << "unexpected statement during synthesis: " << statement.id();
  }
}
