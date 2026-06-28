/*******************************************************************\

Module: Verilog Simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "vl_simulator.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/exit_codes.h>
#include <util/mp_arith.h>
#include <util/std_expr.h>

#include <verilog/verilog_expr.h>

#include <iomanip>
#include <iostream>
#include <sstream>
#include <stdexcept>

/*******************************************************************\

Function: vl_simulatort::simulate

\*******************************************************************/

int vl_simulatort::simulate(const irep_idt &module_symbol)
{
  const auto *sym = symbol_table.lookup(module_symbol);
  if(sym == nullptr)
  {
    error() << "module not found: " << module_symbol << eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }

  if(sym->value.id() != ID_verilog_module)
  {
    error() << "symbol is not a module: " << module_symbol << eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }

  const auto &module_expr =
    static_cast<const verilog_module_exprt &>(sym->value);

  run_module(module_expr);

  if(assertion_failure)
    return CPROVER_EXIT_VERIFICATION_UNSAFE;

  return finish_code.value_or(0);
}

/*******************************************************************\

Function: vl_simulatort::run_module

\*******************************************************************/

void vl_simulatort::run_module(const verilog_module_exprt &module_expr)
{
  // Collect initial blocks. All run concurrently starting at time 0,
  // modelled here as sequential execution.
  for(const auto &item : module_expr.module_items())
  {
    if(item.id() == ID_initial)
    {
      const auto &initial = to_verilog_initial(item);
      run_statement(initial.statement());
      if(finish_code.has_value())
        return;
    }
  }
}

/*******************************************************************\

Function: vl_simulatort::run_statement

\*******************************************************************/

void vl_simulatort::run_statement(const verilog_statementt &statement)
{
  if(finish_code.has_value())
    return;

  const irep_idt &id = statement.id();

  if(id == ID_block)
  {
    for(const auto &s : statement.operands())
    {
      run_statement(to_verilog_statement(s));
      if(finish_code.has_value())
        return;
    }
  }
  else if(id == ID_verilog_blocking_assign)
  {
    const auto &assign = to_verilog_blocking_assign(statement);
    mp_integer value = eval_expr(assign.rhs());
    const exprt &lhs = assign.lhs();
    if(lhs.id() == ID_symbol)
      state[to_symbol_expr(lhs).identifier()] = value;
    else if(lhs.id() == ID_verilog_identifier)
      state[to_verilog_identifier_expr(lhs).scope()] = value;
  }
  else if(id == ID_if)
  {
    const auto &if_stmt = to_verilog_if(statement);
    mp_integer cond = eval_expr(if_stmt.cond());
    if(cond != 0)
      run_statement(if_stmt.then_case());
    else if(if_stmt.has_else_case())
      run_statement(if_stmt.else_case());
  }
  else if(id == ID_for)
  {
    const auto &for_stmt = to_verilog_for(statement);
    for(const auto &init : for_stmt.initialization())
      run_statement(init);
    while(true)
    {
      mp_integer cond = eval_expr(for_stmt.condition());
      if(cond == 0)
        break;
      run_statement(for_stmt.body());
      if(finish_code.has_value())
        return;
      run_statement(for_stmt.inc_statement());
    }
  }
  else if(id == ID_while)
  {
    const auto &while_stmt = to_verilog_while(statement);
    while(true)
    {
      mp_integer cond = eval_expr(while_stmt.condition());
      if(cond == 0)
        break;
      run_statement(while_stmt.body());
      if(finish_code.has_value())
        return;
    }
  }
  else if(id == ID_repeat)
  {
    const auto &repeat_stmt = to_verilog_repeat(statement);
    mp_integer count = eval_expr(repeat_stmt.condition());
    for(mp_integer i = 0; i < count; ++i)
    {
      run_statement(repeat_stmt.body());
      if(finish_code.has_value())
        return;
    }
  }
  else if(id == ID_forever)
  {
    const auto &forever_stmt = to_verilog_forever(statement);
    while(true)
    {
      run_statement(forever_stmt.body());
      if(finish_code.has_value())
        return;
    }
  }
  else if(id == ID_delay)
  {
    const auto &delay_stmt = to_verilog_delay(statement);
    mp_integer delay = eval_expr(delay_stmt.delay_value());
    current_time += delay;
    run_statement(delay_stmt.body());
  }
  else if(id == ID_event_guard)
  {
    // @(event) -- run the body immediately in this simplified model
    const auto &guard = to_verilog_event_guard(statement);
    run_statement(guard.body());
  }
  else if(id == ID_function_call)
  {
    const auto &call = to_verilog_function_call(statement);
    if(call.is_system_function_call())
    {
      const auto base_name = id2string(
        to_verilog_identifier_expr(call.function()).base_name());
      run_system_task(base_name, call.arguments());
    }
  }
  else if(
    id == ID_verilog_immediate_assert ||
    id == ID_verilog_assert_property ||
    id == ID_verilog_smv_assert)
  {
    // Nothing to simulate here; assertions are handled by the model checker.
    // In simulation mode, evaluate the condition and report failures.
    // The condition was stored in operand 0 by the typechecker.
    if(!statement.operands().empty())
    {
      mp_integer cond = eval_expr(statement.operands()[0]);
      if(cond == 0)
      {
        error().source_location = statement.source_location();
        error() << "assertion violation" << eom;
        assertion_failure = true;
      }
    }
  }
  else if(id == ID_skip)
  {
    // nothing
  }
  else if(
    id == ID_verilog_non_blocking_assign ||
    id == ID_procedural_continuous_assign ||
    id == ID_verilog_blocking_assign_plus ||
    id == ID_verilog_blocking_assign_minus ||
    id == ID_verilog_blocking_assign_mult ||
    id == ID_verilog_blocking_assign_div ||
    id == ID_verilog_blocking_assign_mod ||
    id == ID_verilog_blocking_assign_bitand ||
    id == ID_verilog_blocking_assign_bitor ||
    id == ID_verilog_blocking_assign_bitxor ||
    id == ID_verilog_blocking_assign_lshr ||
    id == ID_verilog_blocking_assign_lshl ||
    id == ID_verilog_blocking_assign_ashr ||
    id == ID_verilog_blocking_assign_ashl)
  {
    // Compound assignments: evaluate RHS and update LHS
    const auto &assign = to_verilog_assign(statement);
    mp_integer rhs_val = eval_expr(assign.rhs());
    mp_integer lhs_val = eval_expr(assign.lhs());

    mp_integer new_val;
    if(id == ID_verilog_non_blocking_assign)
      new_val = rhs_val;
    else if(id == ID_verilog_blocking_assign_plus)
      new_val = lhs_val + rhs_val;
    else if(id == ID_verilog_blocking_assign_minus)
      new_val = lhs_val - rhs_val;
    else if(id == ID_verilog_blocking_assign_mult)
      new_val = lhs_val * rhs_val;
    else if(id == ID_verilog_blocking_assign_div && rhs_val != 0)
      new_val = lhs_val / rhs_val;
    else
      new_val = rhs_val;

    const exprt &lhs = assign.lhs();
    if(lhs.id() == ID_symbol)
      state[to_symbol_expr(lhs).identifier()] = new_val;
    else if(lhs.id() == ID_verilog_identifier)
      state[to_verilog_identifier_expr(lhs).scope()] = new_val;
  }
  // silently ignore statements we don't handle
}

/*******************************************************************\

Function: vl_simulatort::run_system_task

\*******************************************************************/

void vl_simulatort::run_system_task(
  const std::string &name,
  const exprt::operandst &args)
{
  if(name == "$display" || name == "$displayb" || name == "$displayh" ||
     name == "$displayo")
  {
    std::string output;
    if(!args.empty() && args[0].type().id() == ID_string)
    {
      // First argument is a format string
      std::size_t arg_index = 1;
      output = format_display(
        id2string(to_constant_expr(args[0]).get_value()), args, arg_index);
    }
    else
    {
      // No format string: print all arguments space-separated
      for(std::size_t i = 0; i < args.size(); ++i)
      {
        if(i > 0)
          output += " ";
        output += integer2string(eval_expr(args[i]));
      }
    }
    std::cout << output << '\n';
  }
  else if(name == "$write" || name == "$writeb" || name == "$writeh" ||
          name == "$writeo")
  {
    if(!args.empty() && args[0].type().id() == ID_string)
    {
      std::size_t arg_index = 1;
      std::cout << format_display(
        id2string(to_constant_expr(args[0]).get_value()), args, arg_index);
    }
    else
    {
      for(std::size_t i = 0; i < args.size(); ++i)
      {
        if(i > 0)
          std::cout << ' ';
        std::cout << integer2string(eval_expr(args[i]));
      }
    }
  }
  else if(name == "$finish")
  {
    int code = 0;
    if(!args.empty())
    {
      mp_integer n = eval_expr(args[0]);
      code = numeric_cast_v<int>(n);
    }
    finish_code = code;
  }
  else if(name == "$fatal")
  {
    // $fatal(severity, message, ...)
    if(!args.empty() && args.size() >= 2 && args[1].type().id() == ID_string)
    {
      std::size_t arg_index = 2;
      std::cerr << "FATAL: "
                << format_display(
                     id2string(to_constant_expr(args[1]).get_value()),
                     args,
                     arg_index)
                << '\n';
    }
    else if(!args.empty() && args[0].type().id() == ID_string)
    {
      std::size_t arg_index = 1;
      std::cerr << "FATAL: "
                << format_display(
                     id2string(to_constant_expr(args[0]).get_value()),
                     args,
                     arg_index)
                << '\n';
    }
    else
    {
      std::cerr << "FATAL\n";
    }
    finish_code = 1;
  }
  else if(name == "$error")
  {
    if(!args.empty() && args[0].type().id() == ID_string)
    {
      std::size_t arg_index = 1;
      std::cerr << "ERROR: "
                << format_display(
                     id2string(to_constant_expr(args[0]).get_value()),
                     args,
                     arg_index)
                << '\n';
    }
    else
    {
      std::cerr << "ERROR\n";
    }
  }
  else if(name == "$warning")
  {
    if(!args.empty() && args[0].type().id() == ID_string)
    {
      std::size_t arg_index = 1;
      std::cout << "WARNING: "
                << format_display(
                     id2string(to_constant_expr(args[0]).get_value()),
                     args,
                     arg_index)
                << '\n';
    }
  }
  else if(name == "$info")
  {
    if(!args.empty() && args[0].type().id() == ID_string)
    {
      std::size_t arg_index = 1;
      std::cout << "INFO: "
                << format_display(
                     id2string(to_constant_expr(args[0]).get_value()),
                     args,
                     arg_index)
                << '\n';
    }
  }
  else if(name == "$stop")
  {
    // Like $finish but with exit code 0
    finish_code = 0;
  }
  else if(name == "$time" || name == "$realtime" || name == "$stime")
  {
    // These are functions, not tasks; ignore as tasks
  }
  // silently ignore other system tasks
}

static std::size_t type_width(const typet &type)
{
  if(type.id() == ID_unsignedbv)
    return to_unsignedbv_type(type).get_width();
  if(type.id() == ID_signedbv)
    return to_signedbv_type(type).get_width();
  if(type.id() == ID_bool)
    return 1;
  return 64; // default for integer, natural, etc.
}

static mp_integer two_power(mp_integer n)
{
  mp_integer result = 1;
  for(mp_integer i = 0; i < n; ++i)
    result *= 2;
  return result;
}

/*******************************************************************\

Function: vl_simulatort::eval_expr

\*******************************************************************/

mp_integer vl_simulatort::eval_expr(const exprt &expr)
{
  const irep_idt &id = expr.id();

  if(id == ID_constant)
  {
    const auto &c = to_constant_expr(expr);
    // String constants are not integers
    if(c.type().id() == ID_string)
      return 0;
    // Handle boolean literals (true_exprt, false_exprt)
    if(c.type().id() == ID_bool)
    {
      if(c.get_value() == ID_true)
        return 1;
      return 0;
    }
    // Four-valued Verilog types: char-per-bit encoding, MSB first.
    // 'x' and 'z' bits are indeterminate; treat as 0 in arithmetic context.
    if(
      c.type().id() == ID_verilog_unsignedbv ||
      c.type().id() == ID_verilog_signedbv)
    {
      const auto &bits = id2string(c.get_value());
      mp_integer result = 0;
      for(char b : bits)
      {
        result *= 2;
        if(b == '1')
          result += 1;
        // '0', 'x', 'z' contribute 0
      }
      return result;
    }
    mp_integer val;
    if(!to_integer(c, val))
      return val;
    // For typeless constants (e.g., in system task arguments), try decimal parse
    const auto &value_str = id2string(c.get_value());
    if(!value_str.empty())
    {
      // Simple decimal integer: all digit characters
      bool all_digits = true;
      for(char ch : value_str)
        if(ch < '0' || ch > '9')
        {
          all_digits = false;
          break;
        }
      if(all_digits)
        return string2integer(value_str);
    }
    return 0;
  }
  else if(id == ID_symbol)
  {
    auto it = state.find(to_symbol_expr(expr).identifier());
    if(it != state.end())
      return it->second;
    return 0;
  }
  else if(id == ID_verilog_identifier)
  {
    const auto &vid = to_verilog_identifier_expr(expr);
    // The scope from the parser is module-relative (e.g., "top.x"),
    // while symbol table identifiers use the "Verilog::$root." prefix.
    // Try the Verilog::$root. prefix first, then the scope as-is.
    if(!vid.scope().empty())
    {
      auto full_id =
        irep_idt{"Verilog::$root." + id2string(vid.scope())};
      auto it = state.find(full_id);
      if(it != state.end())
        return it->second;
      it = state.find(vid.scope());
      if(it != state.end())
        return it->second;
    }
    auto it = state.find(vid.base_name());
    if(it != state.end())
      return it->second;
    return 0;
  }
  else if(id == ID_plus)
  {
    mp_integer result = 0;
    for(const auto &op : expr.operands())
      result += eval_expr(op);
    return result;
  }
  else if(id == ID_minus)
  {
    if(expr.operands().size() == 1)
      return -eval_expr(expr.operands()[0]);
    return eval_expr(expr.operands()[0]) - eval_expr(expr.operands()[1]);
  }
  else if(id == ID_mult)
  {
    mp_integer result = 1;
    for(const auto &op : expr.operands())
      result *= eval_expr(op);
    return result;
  }
  else if(id == ID_div)
  {
    mp_integer lhs = eval_expr(expr.operands()[0]);
    mp_integer rhs = eval_expr(expr.operands()[1]);
    if(rhs == 0)
      return 0;
    return lhs / rhs;
  }
  else if(id == ID_mod)
  {
    mp_integer lhs = eval_expr(expr.operands()[0]);
    mp_integer rhs = eval_expr(expr.operands()[1]);
    if(rhs == 0)
      return 0;
    return lhs % rhs;
  }
  else if(id == ID_equal)
    return mp_integer{
      eval_expr(expr.operands()[0]) == eval_expr(expr.operands()[1]) ? 1 : 0};
  else if(id == ID_notequal)
    return mp_integer{
      eval_expr(expr.operands()[0]) != eval_expr(expr.operands()[1]) ? 1 : 0};
  else if(id == ID_le)
    return mp_integer{
      eval_expr(expr.operands()[0]) <= eval_expr(expr.operands()[1]) ? 1 : 0};
  else if(id == ID_lt)
    return mp_integer{
      eval_expr(expr.operands()[0]) < eval_expr(expr.operands()[1]) ? 1 : 0};
  else if(id == ID_ge)
    return mp_integer{
      eval_expr(expr.operands()[0]) >= eval_expr(expr.operands()[1]) ? 1 : 0};
  else if(id == ID_gt)
    return mp_integer{
      eval_expr(expr.operands()[0]) > eval_expr(expr.operands()[1]) ? 1 : 0};
  else if(id == ID_not)
    return mp_integer{eval_expr(expr.operands()[0]) == 0 ? 1 : 0};
  else if(id == ID_and)
  {
    for(const auto &op : expr.operands())
      if(eval_expr(op) == 0)
        return 0;
    return 1;
  }
  else if(id == ID_or)
  {
    for(const auto &op : expr.operands())
      if(eval_expr(op) != 0)
        return 1;
    return 0;
  }
  else if(id == ID_bitand)
  {
    mp_integer result = eval_expr(expr.operands()[0]);
    for(std::size_t i = 1; i < expr.operands().size(); ++i)
      result = bitwise_and(result, eval_expr(expr.operands()[i]));
    return result;
  }
  else if(id == ID_bitor)
  {
    mp_integer result = eval_expr(expr.operands()[0]);
    for(std::size_t i = 1; i < expr.operands().size(); ++i)
      result = bitwise_or(result, eval_expr(expr.operands()[i]));
    return result;
  }
  else if(id == ID_bitxor)
  {
    mp_integer result = eval_expr(expr.operands()[0]);
    for(std::size_t i = 1; i < expr.operands().size(); ++i)
      result = bitwise_xor(result, eval_expr(expr.operands()[i]));
    return result;
  }
  else if(id == ID_bitnot)
  {
    mp_integer v = eval_expr(expr.operands()[0]);
    std::size_t width = type_width(expr.type());
    mp_integer mask = two_power(mp_integer{width}) - 1;
    return bitwise_xor(v, mask);
  }
  else if(id == ID_lshr)
  {
    std::size_t width = type_width(expr.type());
    return logic_right_shift(
      eval_expr(expr.operands()[0]), eval_expr(expr.operands()[1]), width);
  }
  else if(id == ID_shr)
  {
    std::size_t width = type_width(expr.type());
    return logic_right_shift(
      eval_expr(expr.operands()[0]), eval_expr(expr.operands()[1]), width);
  }
  else if(id == ID_shl)
  {
    std::size_t width = type_width(expr.type());
    return logic_left_shift(
      eval_expr(expr.operands()[0]), eval_expr(expr.operands()[1]), width);
  }
  else if(id == ID_ashr)
  {
    std::size_t width = type_width(expr.type());
    return arith_right_shift(
      eval_expr(expr.operands()[0]), eval_expr(expr.operands()[1]), width);
  }
  else if(id == ID_typecast)
    return eval_expr(expr.operands()[0]);
  else if(id == ID_extractbits)
  {
    mp_integer val = eval_expr(expr.operands()[0]);
    mp_integer upper = eval_expr(expr.operands()[1]);
    mp_integer lower = eval_expr(expr.operands()[2]);
    mp_integer slice_width = upper - lower + 1;
    std::size_t sw = numeric_cast_v<std::size_t>(slice_width);
    mp_integer mask = two_power(mp_integer{sw}) - 1;
    mp_integer shifted =
      logic_right_shift(val, lower, type_width(expr.operands()[0].type()));
    return bitwise_and(shifted, mask);
  }
  else if(id == ID_index)
  {
    mp_integer val = eval_expr(expr.operands()[0]);
    mp_integer idx = eval_expr(expr.operands()[1]);
    mp_integer shifted =
      logic_right_shift(val, idx, type_width(expr.operands()[0].type()));
    return bitwise_and(shifted, mp_integer{1});
  }
  else if(id == ID_concatenation)
  {
    mp_integer result = 0;
    for(const auto &op : expr.operands())
    {
      std::size_t width = type_width(op.type());
      result = logic_left_shift(result, mp_integer{width}, 128) ;
      result = bitwise_or(result, eval_expr(op));
    }
    return result;
  }
  else if(id == ID_verilog_logical_equality)
    return mp_integer{
      eval_expr(expr.operands()[0]) == eval_expr(expr.operands()[1]) ? 1 : 0};
  else if(id == ID_verilog_logical_inequality)
    return mp_integer{
      eval_expr(expr.operands()[0]) != eval_expr(expr.operands()[1]) ? 1 : 0};
  else if(id == ID_verilog_case_equality)
    return mp_integer{
      eval_expr(expr.operands()[0]) == eval_expr(expr.operands()[1]) ? 1 : 0};
  else if(id == ID_verilog_case_inequality)
    return mp_integer{
      eval_expr(expr.operands()[0]) != eval_expr(expr.operands()[1]) ? 1 : 0};
  else if(id == ID_if)
  {
    // Ternary: condition ? then : else
    mp_integer cond = eval_expr(expr.operands()[0]);
    return cond != 0 ? eval_expr(expr.operands()[1]) : eval_expr(expr.operands()[2]);
  }
  // Unknown expression: return 0
  return 0;
}

/*******************************************************************\

Function: vl_simulatort::format_display

\*******************************************************************/

std::string vl_simulatort::format_display(
  const std::string &fmt,
  const exprt::operandst &args,
  std::size_t &arg_index)
{
  std::string result;

  for(std::size_t i = 0; i < fmt.size(); ++i)
  {
    if(fmt[i] == '%' && i + 1 < fmt.size())
    {
      ++i;
      char spec = fmt[i];
      if(spec == '%')
      {
        result += '%';
      }
      else if(spec == 'd' || spec == 'D')
      {
        if(arg_index < args.size())
          result += integer2string(eval_expr(args[arg_index++]));
      }
      else if(spec == 'b' || spec == 'B')
      {
        if(arg_index < args.size())
        {
          mp_integer v = eval_expr(args[arg_index++]);
          if(v == 0)
            result += '0';
          else
          {
            std::string bits;
            mp_integer tmp = v;
            while(tmp > 0)
            {
              bits = (char)('0' + numeric_cast_v<int>(tmp % 2)) + bits;
              tmp /= 2;
            }
            result += bits;
          }
        }
      }
      else if(spec == 'h' || spec == 'H' || spec == 'x' || spec == 'X')
      {
        if(arg_index < args.size())
          result += integer2string(eval_expr(args[arg_index++]), 16);
      }
      else if(spec == 'o' || spec == 'O')
      {
        if(arg_index < args.size())
          result += integer2string(eval_expr(args[arg_index++]), 8);
      }
      else if(spec == 's' || spec == 'S')
      {
        if(arg_index < args.size())
        {
          const auto &arg = args[arg_index++];
          if(arg.type().id() == ID_string)
            result += id2string(to_constant_expr(arg).get_value());
          else
            result += integer2string(eval_expr(arg));
        }
      }
      else if(spec == 't' || spec == 'T')
      {
        // Simulation time
        result += integer2string(current_time);
      }
      else if(spec == 'm' || spec == 'M')
      {
        // Hierarchical module name — use empty for now
        result += "<module>";
      }
      else
      {
        result += '%';
        result += spec;
      }
    }
    else if(fmt[i] == '\\' && i + 1 < fmt.size())
    {
      ++i;
      switch(fmt[i])
      {
      case 'n':
        result += '\n';
        break;
      case 't':
        result += '\t';
        break;
      case '\\':
        result += '\\';
        break;
      case '"':
        result += '"';
        break;
      default:
        result += '\\';
        result += fmt[i];
        break;
      }
    }
    else
    {
      result += fmt[i];
    }
  }

  return result;
}
