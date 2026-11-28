/*******************************************************************\

Module: VHDL Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "vhdl_synthesis.h"
#include "vhdl_synthesis_class.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/mathematical_expr.h>

#include <temporal-logic/ltl.h>
#include <trans-word-level/next_symbol.h>

#include "vhdl_types.h"

const symbolt &vhdl_synthesist::lookup(const symbol_exprt &symbol_expr) const
{
  return symbol_table.lookup_ref(symbol_expr.get_identifier());
}

bool vhdl_synthesist::contains_clock_edge(const exprt &expr)
{
  if(
    expr.id() == ID_vhdl_event || expr.id() == ID_vhdl_rising_edge ||
    expr.id() == ID_vhdl_falling_edge)
    return true;

  // assertions do not affect the timing of assignments
  if(expr.id() == ID_code && to_code(expr).get_statement() == ID_assert)
    return false;

  for(auto &op : expr.operands())
    if(contains_clock_edge(op))
      return true;

  return false;
}

/// the value of a constant of type bit, std_ulogic or boolean, if it
/// is '0', '1', false or true; 'H' and 'L' are not clock edges
static std::optional<bool> bit_value(const exprt &expr)
{
  if(!expr.is_constant())
    return {};

  if(expr.type().id() == ID_bool)
    return expr.is_true();

  if(expr.type().id() != ID_vhdl_enumeration)
    return {};

  auto literal = to_constant_expr(expr).get_value();
  if(literal == "'1'" || literal == "true")
    return true;
  else if(literal == "'0'" || literal == "false")
    return false;
  else
    return {};
}

/// IEEE 1076.6-2004 6.1.3.1: the clock edge conditions are
/// clk'event and clk = '1', clk'event and clk = '0', rising_edge(clk)
/// and falling_edge(clk).
bool vhdl_synthesist::is_clock_edge(const exprt &expr)
{
  std::optional<clockt> this_clock;

  if(expr.id() == ID_vhdl_rising_edge || expr.id() == ID_vhdl_falling_edge)
  {
    auto &signal = to_unary_expr(expr).op();
    if(signal.id() != ID_symbol)
      return false;
    this_clock = clockt{
      to_symbol_expr(signal).get_identifier(),
      expr.id() == ID_vhdl_rising_edge};
  }
  else if(expr.id() == ID_and && expr.operands().size() == 2)
  {
    auto &op0 = to_binary_expr(expr).op0();
    auto &op1 = to_binary_expr(expr).op1();

    // the level the clock is compared with, if this is a level check
    auto level_of =
      [](const exprt &event, const exprt &level) -> std::optional<bool>
    {
      if(event.id() != ID_vhdl_event)
        return {};
      auto &clock = to_unary_expr(event).op();
      if(clock.id() != ID_symbol)
        return {};
      if(level == clock)
        return true;
      if(level.id() == ID_not && to_not_expr(level).op() == clock)
        return false;
      if(level.id() == ID_equal || level.id() == ID_notequal)
      {
        auto &lhs = to_binary_expr(level).lhs();
        auto &rhs = to_binary_expr(level).rhs();
        const exprt *other = lhs == clock   ? &rhs
                             : rhs == clock ? &lhs
                                            : nullptr;
        if(other == nullptr)
          return {};
        auto value = bit_value(*other);
        if(!value.has_value())
          return {};
        return level.id() == ID_equal ? *value : !*value;
      }
      return {};
    };

    auto level = level_of(op0, op1);
    const exprt *event = &op0;
    if(!level.has_value())
    {
      level = level_of(op1, op0);
      event = &op1;
    }

    if(!level.has_value())
      return false;

    this_clock = clockt{
      to_symbol_expr(to_unary_expr(*event).op()).get_identifier(), *level};
  }
  else
    return false;

  // there is one clock
  if(clock.has_value())
  {
    if(
      clock->signal != this_clock->signal ||
      clock->rising != this_clock->rising)
    {
      message.error().source_location = expr.source_location();
      message.error() << "multiple clocks or clock edges are not supported"
                      << messaget::eom;
      throw 0;
    }
  }
  else
    clock = this_clock;

  return true;
}

void vhdl_synthesist::check_no_clock_edge(const exprt &expr) const
{
  if(contains_clock_edge(expr))
  {
    message.error().source_location = expr.source_location();
    message.error() << "clock edge outside of a clock edge condition"
                    << messaget::eom;
    throw 0;
  }
}

exprt vhdl_synthesist::value_of(
  const symbol_exprt &symbol_expr,
  const valuest &values) const
{
  auto v_it = values.find(symbol_expr.get_identifier());
  if(v_it == values.end())
    return symbol_expr;
  else
    return v_it->second;
}

/// Variables see the values assigned earlier in the process
/// (IEEE 1076-2008 10.6.2.1); signals see the value from the
/// beginning of the process (10.5.2.2).
exprt vhdl_synthesist::substitute(exprt expr, const valuest &values) const
{
  if(expr.id() == ID_symbol)
  {
    auto &symbol_expr = to_symbol_expr(expr);
    auto &symbol = lookup(symbol_expr);
    if(symbol.is_auxiliary) // a variable
      return value_of(symbol_expr, values);
    else
      return expr;
  }
  else
  {
    for(auto &op : expr.operands())
      op = substitute(std::move(op), values);
    return expr;
  }
}

exprt vhdl_synthesist::current_value(exprt target, const valuest &values) const
{
  if(target.id() == ID_symbol)
    return value_of(to_symbol_expr(target), values);
  else
  {
    // the object is operand 0
    auto &object = target.operands().front();
    object = current_value(object, values);
    return target;
  }
}

exprt vhdl_synthesist::substitute_indices(exprt target, const valuest &values)
  const
{
  if(target.id() == ID_symbol)
    return target;
  else
  {
    auto &operands = target.operands();
    operands.front() = substitute_indices(operands.front(), values);
    for(std::size_t i = 1; i < operands.size(); i++)
      operands[i] = substitute(operands[i], values);
    return target;
  }
}

/// a slice of a vector, with a static range
static exprt make_slice(const exprt &vector, const vhdl_ranget &range)
{
  auto &vector_type = to_vhdl_array_type(vector.type());
  vhdl_range_exprt range_expr{
    vhdl_integer_constant(range.left, vhdl_integer_type()),
    to_irep_id(range.direction),
    vhdl_integer_constant(range.right, vhdl_integer_type())};
  vhdl_slice_exprt result{vector, std::move(range_expr)};
  result.type() = vhdl_constrained_array_type(vector_type, range);
  return std::move(result);
}

/// IEEE 1076-2008 10.5.2.1: the target may be a name, an indexed name,
/// a slice, or a selected name. We compute the new value of the
/// entire object, as a VHDL-typed expression.
/// An array value keeps its own index range, which may differ from
/// that of the object it is assigned to (IEEE 1076-2008 10.5.2.2); the
/// value of the object gets the object's subtype. The lowering drops
/// the conversion, as both map to the same CBMC type.
exprt vhdl_synthesist::with_type(exprt value, const typet &type)
{
  if(value.type() == type)
    return value;
  else
    return typecast_exprt{std::move(value), type};
}

exprt vhdl_synthesist::assign_to(
  const exprt &lhs,
  exprt rhs,
  const valuest &values) const
{
  if(lhs.id() == ID_symbol)
  {
    return with_type(std::move(rhs), lhs.type());
  }
  else if(lhs.id() == ID_index)
  {
    // one element of an array or vector
    auto &array = to_binary_expr(lhs).op0();
    auto &index = to_binary_expr(lhs).op1();
    auto old_value = current_value(array, values);
    with_exprt new_value{std::move(old_value), index, std::move(rhs)};
    return assign_to(array, std::move(new_value), values);
  }
  else if(lhs.id() == ID_vhdl_slice)
  {
    // A slice of a vector; the bounds are static. The new value is the
    // concatenation of the elements before the slice, the slice, and
    // the elements after it.
    auto &slice = to_vhdl_slice_expr(lhs);
    auto &vector = slice.prefix();
    auto &vector_type = to_vhdl_array_type(vector.type());
    auto vector_range = vector_type.range();
    auto slice_range = to_vhdl_array_type(lhs.type()).range();
    auto old_value = current_value(vector, values);

    exprt::operandst parts;

    // the elements before the slice, from the left
    vhdl_ranget before, after;
    if(vector_range.direction == vhdl_directiont::DOWNTO)
    {
      before = {
        vector_range.high(), slice_range.high() + 1, vhdl_directiont::DOWNTO};
      after = {
        slice_range.low() - 1, vector_range.low(), vhdl_directiont::DOWNTO};
    }
    else
    {
      before = {vector_range.low(), slice_range.low() - 1, vhdl_directiont::TO};
      after = {
        slice_range.high() + 1, vector_range.high(), vhdl_directiont::TO};
    }

    if(before.length() != 0)
      parts.push_back(make_slice(old_value, before));

    parts.push_back(std::move(rhs));

    if(after.length() != 0)
      parts.push_back(make_slice(old_value, after));

    exprt new_value;
    if(parts.size() == 1)
    {
      new_value = std::move(parts.front());
      new_value.type() = vector.type();
    }
    else
      new_value = concatenation_exprt{std::move(parts), vector.type()};

    return assign_to(vector, std::move(new_value), values);
  }
  else if(lhs.id() == ID_member)
  {
    auto &member = to_vhdl_member_expr(lhs);
    auto old_value = current_value(member.compound(), values);
    exprt where(ID_member_name);
    where.set(ID_component_name, member.get_component_name());
    auto new_value = with_exprt{old_value, where, rhs};
    return assign_to(member.compound(), std::move(new_value), values);
  }
  else
  {
    message.error().source_location = lhs.source_location();
    message.error() << "unexpected assignment target: " << lhs.id()
                    << messaget::eom;
    throw 0;
  }
}

void vhdl_synthesist::execute_assign(
  const vhdl_code_assignt &code,
  const exprt &guard,
  valuest &values,
  bool clocked)
{
  auto lhs = substitute_indices(code.target(), values);
  auto &rhs = code.value();

  // find the object
  exprt base = lhs;
  while(base.id() != ID_symbol)
    base = base.operands().front();

  auto &symbol_expr = to_symbol_expr(base);
  auto &symbol = lookup(symbol_expr);

  // s <= unaffected;
  if(rhs.is_nil())
    return;

  // IEEE 1076-2008 6.4.2.3: one driver per signal; the resolution
  // of multiple drivers is not supported
  auto driver_entry = drivers.emplace(symbol.name, current_driver);
  if(!driver_entry.second && driver_entry.first->second != current_driver)
  {
    message.error().source_location = code.source_location();
    message.error() << "`" << symbol.base_name << "' has multiple drivers"
                    << messaget::eom;
    throw 0;
  }

  // The value is an expression, or nested if expressions with a
  // nil else branch when there is none (the VHDL-2008 conditional
  // assignment). A nil means the object is unaffected.
  std::function<exprt(const exprt &)> value_rec = [&](const exprt &v) -> exprt
  {
    if(v.id() == ID_if)
    {
      auto &if_expr = to_if_expr(v);

      // IEEE 1076.6-2004 6.1.3.3: q <= d when rising_edge(clk);
      if(contains_clock_edge(if_expr.cond()))
      {
        if(!is_clock_edge(if_expr.cond()) || !clocked)
        {
          message.error().source_location = if_expr.source_location();
          message.error() << "unsupported clock edge condition"
                          << messaget::eom;
          throw 0;
        }

        if(if_expr.false_case().is_not_nil())
        {
          message.error().source_location = if_expr.source_location();
          message.error() << "else branch on a clock edge condition"
                          << messaget::eom;
          throw 0;
        }

        return value_rec(if_expr.true_case());
      }

      auto cond = substitute(if_expr.cond(), values);
      auto true_case = value_rec(if_expr.true_case());
      auto false_case = if_expr.false_case().is_nil()
                          ? value_of(symbol_expr, values)
                          : value_rec(if_expr.false_case());
      return if_exprt{
        std::move(cond), std::move(true_case), std::move(false_case)};
    }
    else
      return assign_to(lhs, substitute(v, values), values);
  };

  // The guard is applied when the branches of an if statement are
  // merged, so the value is unconditional here.
  // The expressions have VHDL types, which the simplifier does not
  // know; simplification is done after lowering.
  values[symbol.name] = value_rec(rhs);
}

void vhdl_synthesist::execute(
  const codet &code,
  const exprt &guard,
  valuest &values,
  bool clocked)
{
  auto statement = code.get_statement();

  if(statement == ID_block)
  {
    for(auto &s : to_code_block(code).statements())
      execute(s, guard, values, clocked);
  }
  else if(statement == ID_skip)
  {
  }
  else if(statement == ID_assign || statement == ID_vhdl_signal_assign)
  {
    execute_assign(to_vhdl_code_assign(code), guard, values, clocked);
  }
  else if(statement == ID_ifthenelse)
  {
    auto &if_code = to_code_ifthenelse(code);
    auto cond = if_code.cond();

    if(contains_clock_edge(cond))
    {
      if(!is_clock_edge(cond))
      {
        message.error().source_location = cond.source_location();
        message.error() << "unsupported clock edge condition" << messaget::eom;
        throw 0;
      }

      if(!clocked)
      {
        message.error().source_location = cond.source_location();
        message.error() << "clock edge in a combinational process"
                        << messaget::eom;
        throw 0;
      }

      // IEEE 1076.6-2004 6.1.3.1: no else branch on the clock edge
      if(if_code.has_else_case())
      {
        message.error().source_location = cond.source_location();
        message.error() << "else branch on a clock edge condition"
                        << messaget::eom;
        throw 0;
      }

      // The body is executed when the clock ticks, which is
      // every cycle.
      execute(if_code.then_case(), guard, values, clocked);
      return;
    }

    cond = substitute(cond, values);

    // execute both branches
    valuest then_values = values, else_values = values;

    execute(
      if_code.then_case(),
      guard.is_true() ? cond : exprt{and_exprt{guard, cond}},
      then_values,
      clocked);

    if(if_code.has_else_case())
    {
      // the condition has a VHDL type
      exprt not_cond = unary_exprt{ID_not, cond, cond.type()};
      execute(
        if_code.else_case(),
        guard.is_true() ? not_cond : exprt{and_exprt{guard, not_cond}},
        else_values,
        clocked);
    }

    // merge: an object that is assigned in one branch only keeps its
    // value from before the if statement in the other branch
    std::set<irep_idt> assigned;
    for(auto &entry : then_values)
      assigned.insert(entry.first);
    for(auto &entry : else_values)
      assigned.insert(entry.first);

    for(auto &identifier : assigned)
    {
      auto &symbol = symbol_table.lookup_ref(identifier);
      symbol_exprt symbol_expr{symbol.name, symbol.type};
      auto old_value = value_of(symbol_expr, values);

      auto t_it = then_values.find(identifier);
      auto e_it = else_values.find(identifier);
      const exprt &then_value =
        t_it == then_values.end() ? old_value : t_it->second;
      const exprt &else_value =
        e_it == else_values.end() ? old_value : e_it->second;

      if(then_value == else_value)
        values[identifier] = then_value;
      else
        values[identifier] = if_exprt{cond, then_value, else_value};
    }
  }
  else if(statement == ID_assert)
  {
    auto &assertion = to_vhdl_code_assert(code);
    auto condition = substitute(assertion.condition(), values);
    if(!guard.is_true())
      condition = implies_exprt{guard, condition};

    synth_property(
      condition,
      assertion.label(),
      assertion.report(),
      assertion.source_location());
  }
  else
  {
    message.error().source_location = code.source_location();
    message.error() << "unexpected statement during synthesis: " << statement
                    << messaget::eom;
    throw 0;
  }
}

void vhdl_synthesist::synth_property(
  const exprt &condition,
  irep_idt label,
  const exprt &report,
  const source_locationt &source_location)
{
  symbolt new_symbol;

  if(label.empty())
    new_symbol.base_name = "property" + std::to_string(++property_counter);
  else
    new_symbol.base_name = label;

  new_symbol.name =
    id2string(module_symbol->name) + "." + id2string(new_symbol.base_name);
  new_symbol.pretty_name = id2string(module_symbol->pretty_name) + "." +
                           id2string(new_symbol.base_name);
  new_symbol.is_property = true;
  new_symbol.mode = ID_VHDL;
  new_symbol.type = bool_typet();
  new_symbol.module = module_symbol->name;
  new_symbol.location = source_location;

  // clock edges have no meaning in a property
  check_no_clock_edge(condition);

  // there is an implicit 'always'
  new_symbol.value = G_exprt{condition};

  if(report.id() == ID_constant && report.type().id() == ID_string)
  {
    new_symbol.location.set_comment(
      "assertion " + id2string(to_constant_expr(report).get_value()));
  }
  else
    new_symbol.location.set_comment("assertion");

  if(symbol_table.add(new_symbol))
  {
    message.error().source_location = source_location;
    message.error() << "duplicate property `" << new_symbol.base_name << "'"
                    << messaget::eom;
    throw 0;
  }
}

void vhdl_synthesist::synth_statement(const codet &code, bool clocked)
{
  current_driver++;

  valuest values;
  execute(code, true_exprt{}, values, clocked);

  for(auto &entry : values)
  {
    auto &symbol = symbol_table.get_writeable_ref(entry.first);
    symbol_exprt symbol_expr{symbol.name, symbol.type};

    check_no_clock_edge(entry.second);

    if(clocked)
    {
      // Variables and signals assigned in a clocked process are
      // state variables with a next-state function.
      symbol.is_state_var = true;
      symbol.is_input = false; // for inout ports
      trans.push_back(
        equal_exprt{next_symbol_exprt{symbol_expr}, entry.second});
    }
    else if(has_symbol_expr(entry.second, symbol.name, false))
    {
      // IEEE 1076.6-2004 6.2.1.2: an incomplete assignment in a
      // combinational process infers a latch, which holds its value
      // when it is not assigned. The value in the next state depends on
      // the inputs in the next state and the latch's current value.
      message.warning().source_location = code.source_location();
      message.warning() << "latch inferred for `" << symbol.base_name << "'"
                        << messaget::eom;

      exprt next_value = entry.second;
      next_value.visit_post(
        [&symbol_expr](exprt &e)
        {
          if(e.id() == ID_symbol && e != symbol_expr)
            e = next_symbol_exprt{to_symbol_expr(e)};
        });

      symbol.is_state_var = true;
      symbol.is_input = false;
      trans.push_back(
        equal_exprt{next_symbol_exprt{symbol_expr}, std::move(next_value)});
    }
    else
    {
      // combinational; the declaration initializer does not apply
      combinational_signals.insert(symbol.name);
      invar.push_back(equal_exprt{symbol_expr, entry.second});
    }
  }
}

/// IEEE 1076.6-2004 6.1.3.1: a clocked process has one of the forms
///
///   if clock_edge then ... end if;
///   if reset_condition then ... elsif clock_edge then ... end if;
///
/// where the reset conditions do not contain a clock edge. Any other
/// use of a clock edge is rejected; a process without a clock edge is
/// combinational.
bool vhdl_synthesist::is_clocked_process(const code_blockt &body) const
{
  auto &statements = body.statements();

  // the clock edge is in an if statement
  bool found_edge = false;

  for(auto &statement : statements)
  {
    if(statement.get_statement() != ID_ifthenelse)
    {
      if(contains_clock_edge(statement))
      {
        message.error().source_location = statement.source_location();
        message.error() << "clock edge in an unsupported position"
                        << messaget::eom;
        throw 0;
      }
      continue;
    }

    // follow the chain of if/elsif
    const codet *if_statement = &statement;
    bool statement_has_edge = false;

    while(if_statement != nullptr)
    {
      auto &if_code = to_code_ifthenelse(*if_statement);

      if(contains_clock_edge(if_code.cond()))
      {
        statement_has_edge = true;
        // the clocked branch may not contain further edges, and there
        // is no else branch (checked when executing)
        if(contains_clock_edge(if_code.then_case()))
        {
          message.error().source_location = if_code.source_location();
          message.error() << "nested clock edge" << messaget::eom;
          throw 0;
        }
        break;
      }

      // a reset branch: no clock edge
      if(contains_clock_edge(if_code.then_case()))
      {
        message.error().source_location = if_code.source_location();
        message.error() << "clock edge in an unsupported position"
                        << messaget::eom;
        throw 0;
      }

      if(!if_code.has_else_case())
        break;

      if(if_code.else_case().get_statement() == ID_ifthenelse)
        if_statement = &if_code.else_case();
      else
      {
        if(contains_clock_edge(if_code.else_case()))
        {
          message.error().source_location = if_code.source_location();
          message.error() << "clock edge in an unsupported position"
                          << messaget::eom;
          throw 0;
        }
        if_statement = nullptr;
      }
    }

    if(statement_has_edge)
    {
      if(found_edge || statements.size() != 1)
      {
        message.error().source_location = statement.source_location();
        message.error()
          << "a clocked process must consist of a single if statement"
          << messaget::eom;
        throw 0;
      }
      found_edge = true;
    }
  }

  return found_edge;
}

void vhdl_synthesist::synth_process(const vhdl_processt &process)
{
  // the type checker produces a block
  auto &body = to_code_block(to_code(process.body()));
  synth_statement(body, is_clocked_process(body));
}

void vhdl_synthesist::synth_module(const irept &module)
{
  PRECONDITION(module.id() == ID_module);

  const exprt &body = static_cast<const exprt &>(module.find(ID_body));

  for(auto &op : body.operands())
  {
    if(op.id() == ID_process)
      synth_process(to_vhdl_process(op));
    else if(op.id() == ID_code)
    {
      auto &code = to_code(op);
      auto statement = code.get_statement();

      if(statement == ID_assert)
      {
        // a concurrent assertion
        auto &assertion = to_vhdl_code_assert(code);
        synth_property(
          assertion.condition(),
          assertion.label(),
          assertion.report(),
          assertion.source_location());
      }
      else
      {
        // concurrent signal assignments, possibly selected or
        // conditional; the condition may be a clock edge
        synth_statement(code, contains_clock_edge(code));
      }
    }
    else
    {
      message.error().source_location = op.source_location();
      message.error() << "unexpected module item during synthesis: " << op.id()
                      << messaget::eom;
      throw 0;
    }
  }

  // Initial values, and the state variables that are not assigned
  // by any clocked process or combinational statement hold their value.
  for(auto &entry : symbol_table.symbols)
  {
    auto &symbol = entry.second;

    if(symbol.module != module_symbol->name || !symbol.is_state_var)
      continue;

    symbol_exprt symbol_expr{symbol.name, symbol.type};

    // The initial value of a signal with a combinational driver is
    // the value of the driver (IEEE 1076-2008 14.7.3.4), and not the
    // value in the declaration, which is overwritten in the first
    // simulation cycle.
    if(
      symbol.value.is_not_nil() &&
      combinational_signals.find(symbol.name) == combinational_signals.end())
    {
      check_no_clock_edge(symbol.value);
      init.push_back(
        equal_exprt{symbol_expr, with_type(symbol.value, symbol.type)});
    }

    if(drivers.find(symbol.name) == drivers.end())
      trans.push_back(equal_exprt{next_symbol_exprt{symbol_expr}, symbol_expr});
  }

  // IEEE 1076-2008 5.2.1: the value of an object of an integer subtype
  // is in the range of the subtype. The design cannot violate this for
  // its inputs, so this is a constraint on the environment.
  for(auto &entry : symbol_table.symbols)
  {
    auto &symbol = entry.second;

    if(symbol.module != module_symbol->name || !symbol.is_input)
      continue;

    if(is_vhdl_integer_type(symbol.type))
    {
      auto range = to_vhdl_integer_type(symbol.type).range();

      // integer itself needs no constraint
      if(range.low() == -power(2, 31) && range.high() == power(2, 31) - 1)
        continue;

      symbol_exprt symbol_expr{symbol.name, symbol.type};
      invar.push_back(and_exprt{
        binary_relation_exprt{
          vhdl_integer_constant(range.low(), symbol.type), ID_le, symbol_expr},
        binary_relation_exprt{
          symbol_expr,
          ID_le,
          vhdl_integer_constant(range.high(), symbol.type)}});
    }
  }

  for(auto &c : invar)
    check_no_clock_edge(c);
}

bool vhdl_synthesist::operator()()
{
  try
  {
    auto s_it=symbol_table.get_writeable(module);

    if(s_it==nullptr)
    {
      message.error() << "module `" << module << "' not found" << messaget::eom;
      throw 0;
    }

    symbolt &symbol = *s_it;
    module_symbol = &symbol;

    property_counter = 0;

    synth_module(symbol.value);

    transt trans_expr{
      ID_trans,
      conjunction(invar),
      conjunction(init),
      conjunction(trans),
      symbol.type};

    symbol.value = trans_expr;

    return false;
  }
  catch(int)
  {
    return true;
  }
}

bool vhdl_synthesis(
  symbol_table_baset &symbol_table,
  irep_idt module,
  message_handlert &message_handler)
{
  return vhdl_synthesist(symbol_table, module, message_handler)();
}
