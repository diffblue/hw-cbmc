/*******************************************************************\

Module: Verilog Simulator

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "vl_simulator.h"

#include <util/arith_tools.h>
#include <util/exit_codes.h>
#include <util/std_expr.h>

#include <verilog/verilog_expr.h>

#include <iostream>

/*******************************************************************\

Function: vl_simulatort::simulate

\*******************************************************************/

int vl_simulatort::simulate(const irep_idt &module_symbol)
{
  const auto *sym = symbol_table.lookup(module_symbol);
  if(sym == nullptr)
  {
    log.error() << "module not found: " << module_symbol << messaget::eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }

  if(sym->value.id() != ID_verilog_module)
  {
    log.error() << "symbol is not a module: " << module_symbol << messaget::eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }

  const auto &module_expr =
    static_cast<const verilog_module_exprt &>(sym->value);

  run_module(module_expr);

  if(sim_state.assertion_failure)
    return CPROVER_EXIT_VERIFICATION_UNSAFE;

  return sim_state.finish_code.value_or(0);
}

/*******************************************************************\

Function: vl_simulatort::run_module

\*******************************************************************/

void vl_simulatort::run_module(const verilog_module_exprt &module_expr)
{
  for(const auto &item : module_expr.module_items())
  {
    if(item.id() == ID_initial)
    {
      const auto &initial = to_verilog_initial(item);
      run_statement(initial.statement());
      if(sim_state.finish_code.has_value())
        return;
    }
  }
}

/*******************************************************************\

Function: vl_simulatort::run_statement

\*******************************************************************/

void vl_simulatort::run_statement(const verilog_statementt &statement)
{
  if(sim_state.finish_code.has_value())
    return;

  const irep_idt &id = statement.id();

  if(id == ID_block)
  {
    for(const auto &s : statement.operands())
    {
      run_statement(to_verilog_statement(s));
      if(sim_state.finish_code.has_value())
        return;
    }
  }
  else if(id == ID_verilog_blocking_assign)
  {
    const auto &assign = to_verilog_blocking_assign(statement);
    mp_integer value = sim_state.eval_expr(assign.rhs());
    const exprt &lhs = assign.lhs();
    if(lhs.id() == ID_symbol)
      sim_state.state[to_symbol_expr(lhs).identifier()] = value;
    else if(lhs.id() == ID_verilog_identifier)
      sim_state.state[to_verilog_identifier_expr(lhs).scope()] = value;
  }
  else if(id == ID_if)
  {
    const auto &if_stmt = to_verilog_if(statement);
    mp_integer cond = sim_state.eval_expr(if_stmt.cond());
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
      mp_integer cond = sim_state.eval_expr(for_stmt.condition());
      if(cond == 0)
        break;
      run_statement(for_stmt.body());
      if(sim_state.finish_code.has_value())
        return;
      run_statement(for_stmt.inc_statement());
    }
  }
  else if(id == ID_while)
  {
    const auto &while_stmt = to_verilog_while(statement);
    while(true)
    {
      mp_integer cond = sim_state.eval_expr(while_stmt.condition());
      if(cond == 0)
        break;
      run_statement(while_stmt.body());
      if(sim_state.finish_code.has_value())
        return;
    }
  }
  else if(id == ID_repeat)
  {
    const auto &repeat_stmt = to_verilog_repeat(statement);
    mp_integer count = sim_state.eval_expr(repeat_stmt.condition());
    for(mp_integer i = 0; i < count; ++i)
    {
      run_statement(repeat_stmt.body());
      if(sim_state.finish_code.has_value())
        return;
    }
  }
  else if(id == ID_forever)
  {
    const auto &forever_stmt = to_verilog_forever(statement);
    while(true)
    {
      run_statement(forever_stmt.body());
      if(sim_state.finish_code.has_value())
        return;
    }
  }
  else if(id == ID_delay)
  {
    const auto &delay_stmt = to_verilog_delay(statement);
    mp_integer delay = sim_state.eval_expr(delay_stmt.delay_value());
    sim_state.current_time += delay;
    run_statement(delay_stmt.body());
  }
  else if(id == ID_event_guard)
  {
    const auto &guard = to_verilog_event_guard(statement);
    run_statement(guard.body());
  }
  else if(id == ID_function_call)
  {
    const auto &call = to_verilog_function_call(statement);
    if(call.is_system_function_call())
    {
      const auto base_name =
        id2string(to_verilog_identifier_expr(call.function()).base_name());
      run_system_task(base_name, call.arguments());
    }
  }
  else if(
    id == ID_verilog_immediate_assert || id == ID_verilog_assert_property ||
    id == ID_verilog_smv_assert)
  {
    if(!statement.operands().empty())
    {
      mp_integer cond = sim_state.eval_expr(statement.operands()[0]);
      if(cond == 0)
      {
        log.error().source_location = statement.source_location();
        log.error() << "assertion violation" << messaget::eom;
        sim_state.assertion_failure = true;
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
    const auto &assign = to_verilog_assign(statement);
    mp_integer rhs_val = sim_state.eval_expr(assign.rhs());
    mp_integer lhs_val = sim_state.eval_expr(assign.lhs());

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
      sim_state.state[to_symbol_expr(lhs).identifier()] = new_val;
    else if(lhs.id() == ID_verilog_identifier)
      sim_state.state[to_verilog_identifier_expr(lhs).scope()] = new_val;
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
  if(
    name == "$display" || name == "$displayb" || name == "$displayh" ||
    name == "$displayo")
  {
    std::string output;
    if(!args.empty() && args[0].type().id() == ID_string)
    {
      std::size_t arg_index = 1;
      output = format_display(
        id2string(to_constant_expr(args[0]).get_value()), args, arg_index);
    }
    else
    {
      for(std::size_t i = 0; i < args.size(); ++i)
      {
        if(i > 0)
          output += " ";
        output += integer2string(sim_state.eval_expr(args[i]));
      }
    }
    std::cout << output << '\n';
  }
  else if(
    name == "$write" || name == "$writeb" || name == "$writeh" ||
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
        std::cout << integer2string(sim_state.eval_expr(args[i]));
      }
    }
  }
  else if(name == "$finish")
  {
    int code = 0;
    if(!args.empty())
    {
      mp_integer n = sim_state.eval_expr(args[0]);
      code = numeric_cast_v<int>(n);
    }
    sim_state.finish_code = code;
  }
  else if(name == "$fatal")
  {
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
    sim_state.finish_code = 1;
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
    sim_state.finish_code = 0;
  }
  else if(name == "$time" || name == "$realtime" || name == "$stime")
  {
    // These are functions, not tasks; ignore as tasks
  }
  // silently ignore other system tasks
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
          result += integer2string(sim_state.eval_expr(args[arg_index++]));
      }
      else if(spec == 'b' || spec == 'B')
      {
        if(arg_index < args.size())
        {
          mp_integer v = sim_state.eval_expr(args[arg_index++]);
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
          result += integer2string(sim_state.eval_expr(args[arg_index++]), 16);
      }
      else if(spec == 'o' || spec == 'O')
      {
        if(arg_index < args.size())
          result += integer2string(sim_state.eval_expr(args[arg_index++]), 8);
      }
      else if(spec == 's' || spec == 'S')
      {
        if(arg_index < args.size())
        {
          const auto &arg = args[arg_index++];
          if(arg.type().id() == ID_string)
            result += id2string(to_constant_expr(arg).get_value());
          else
            result += integer2string(sim_state.eval_expr(arg));
        }
      }
      else if(spec == 't' || spec == 'T')
      {
        result += integer2string(sim_state.current_time);
      }
      else if(spec == 'm' || spec == 'M')
      {
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
