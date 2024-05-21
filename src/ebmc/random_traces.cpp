/*******************************************************************\

Module: Random Trace Generation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "random_traces.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/console.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/string2int.h>
#include <util/unicode.h>

#include <solvers/flattening/boolbv.h>
#include <solvers/sat/satcheck.h>
#include <trans-word-level/instantiate_word_level.h>
#include <trans-word-level/trans_trace_word_level.h>
#include <trans-word-level/unwind.h>

#include "ebmc_base.h"
#include "ebmc_error.h"
#include "waveform.h"

#include <algorithm>
#include <random>

/*******************************************************************\

   Class: random_tracest

 Purpose:

\*******************************************************************/

class random_tracest
{
public:
  explicit random_tracest(
    const transition_systemt &_transition_system,
    message_handlert &_message_handler)
    : transition_system(_transition_system),
      ns(_transition_system.symbol_table),
      message(_message_handler)
  {
  }

  void operator()(
    std::function<void(trans_tracet)> consumer,
    std::size_t random_seed,
    std::size_t number_of_traces,
    std::size_t number_of_trace_steps);

protected:
  const transition_systemt &transition_system;
  const namespacet ns;
  messaget message;

  using symbolst = std::vector<symbol_exprt>;

  std::vector<exprt> random_input_constraints(
    decision_proceduret &,
    const symbolst &inputs,
    size_t number_of_timeframes);

  std::vector<exprt> random_initial_state_constraints(
    decision_proceduret &,
    const symbolst &state_variables);

  static std::vector<exprt>
  merge_constraints(const std::vector<exprt> &a, const std::vector<exprt> &b)
  {
    std::vector<exprt> result;
    result.reserve(a.size() + b.size());
    result.insert(result.end(), a.begin(), a.end());
    result.insert(result.end(), b.begin(), b.end());
    return result;
  }

  constant_exprt random_value(const typet &);

  symbolst inputs() const;
  symbolst state_variables() const;
  symbolst remove_constrained(const symbolst &) const;

  void
  freeze(const symbolst &, std::size_t number_of_timeframes, boolbvt &) const;

  // Random number generator. These are fully specified in
  // the C++ standard, and produce the same values on compliant
  // implementations.
  std::mt19937 generator;
  bool random_bit();
};

/*******************************************************************\

Function: random_traces

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int random_traces(const cmdlinet &cmdline, message_handlert &message_handler)
{
  const auto number_of_traces = [&cmdline]() -> std::size_t
  {
    if(cmdline.isset("traces"))
    {
      auto number_of_traces_opt =
        string2optional_size_t(cmdline.get_value("traces"));

      if(!number_of_traces_opt.has_value())
        throw ebmc_errort() << "failed to parse number of traces";

      return number_of_traces_opt.value();
    }
    else
      return 10; // default
  }();

  const std::size_t random_seed = [&cmdline]() -> std::size_t
  {
    if(cmdline.isset("random-seed"))
    {
      auto random_seed_opt =
        string2optional_size_t(cmdline.get_value("random-seed"));

      if(!random_seed_opt.has_value())
        throw ebmc_errort() << "failed to parse random seed";

      return random_seed_opt.value();
    }
    else
      return 0;
  }();

  const std::size_t number_of_trace_steps = [&cmdline]() -> std::size_t
  {
    if(cmdline.isset("trace-steps"))
    {
      auto trace_steps_opt =
        string2optional_size_t(cmdline.get_value("trace-steps"));

      if(!trace_steps_opt.has_value())
        throw ebmc_errort() << "failed to parse number of trace steps";

      return trace_steps_opt.value();
    }
    else
      return 10; // default
  }();

  const auto outfile_prefix = [&cmdline]() -> std::optional<std::string> {
    if(cmdline.isset("vcd"))
      return cmdline.get_value("vcd") + ".";
    else
      return {};
  }();

  transition_systemt transition_system =
    get_transition_system(cmdline, message_handler);

  if(cmdline.isset("waveform") && cmdline.isset("vcd"))
    throw ebmc_errort() << "cannot do VCD and ASCII waveform simultaneously";

  auto consumer = [&, trace_nr = 0ull](trans_tracet trace) mutable -> void {
    namespacet ns(transition_system.symbol_table);
    if(cmdline.isset("vcd"))
    {
      PRECONDITION(outfile_prefix.has_value());
      auto filename = outfile_prefix.value() + std::to_string(trace_nr + 1);
      std::ofstream out(widen_if_needed(filename));

      if(!out)
        throw ebmc_errort() << "failed to write trace to " << filename;

      consolet::out() << "*** Writing " << filename << '\n';

      messaget message(message_handler);
      show_trans_trace_vcd(trace, message, ns, out);
    }
    else if(cmdline.isset("waveform"))
    {
      consolet::out() << "*** Trace " << (trace_nr + 1) << '\n';
      show_waveform(trace, ns);
    }
    else if(cmdline.isset("numbered-trace"))
    {
      consolet::out() << "*** Trace " << (trace_nr + 1) << '\n';
      messaget message(message_handler);
      show_trans_trace_numbered(trace, message, ns, consolet::out());
    }
    else // default
    {
      consolet::out() << "*** Trace " << (trace_nr + 1) << '\n';
      messaget message(message_handler);
      show_trans_trace(trace, message, ns, consolet::out());
    }

    trace_nr++;
  };

  random_tracest(transition_system, message_handler)(
    consumer, random_seed, number_of_traces, number_of_trace_steps);

  return 0;
}

/*******************************************************************\

Function: random_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int random_trace(const cmdlinet &cmdline, message_handlert &message_handler)
{
  if(cmdline.isset("traces"))
    throw ebmc_errort() << "must not give number of traces";

  const std::size_t random_seed = [&cmdline]() -> std::size_t {
    if(cmdline.isset("random-seed"))
    {
      auto random_seed_opt =
        string2optional_size_t(cmdline.get_value("random-seed"));

      if(!random_seed_opt.has_value())
        throw ebmc_errort() << "failed to parse random seed";

      return random_seed_opt.value();
    }
    else
      return 0;
  }();

  const std::size_t number_of_trace_steps = [&cmdline]() -> std::size_t {
    if(cmdline.isset("trace-steps"))
    {
      auto trace_steps_opt =
        string2optional_size_t(cmdline.get_value("trace-steps"));

      if(!trace_steps_opt.has_value())
        throw ebmc_errort() << "failed to parse number of trace steps";

      return trace_steps_opt.value();
    }
    else if(cmdline.isset("bound"))
    {
      auto bound_opt = string2optional_size_t(cmdline.get_value("bound"));

      if(!bound_opt.has_value())
        throw ebmc_errort() << "failed to parse bound";

      return bound_opt.value();
    }
    else
      return 10; // default
  }();

  transition_systemt transition_system =
    get_transition_system(cmdline, message_handler);

  auto consumer = [&](trans_tracet trace) -> void {
    namespacet ns(transition_system.symbol_table);
    if(cmdline.isset("random-waveform") || cmdline.isset("waveform"))
    {
      show_waveform(trace, ns);
    }
    else if(cmdline.isset("numbered-trace"))
    {
      messaget message(message_handler);
      show_trans_trace_numbered(trace, message, ns, consolet::out());
    }
    else // default
    {
      messaget message(message_handler);
      show_trans_trace(trace, message, ns, consolet::out());
    }
  };

  random_tracest(transition_system, message_handler)(
    consumer, random_seed, 1, number_of_trace_steps);

  return 0;
}

/*******************************************************************\

Function: random_traces

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void random_traces(
  const transition_systemt &transition_system,
  const std::string &outfile_prefix,
  std::size_t number_of_traces,
  std::size_t number_of_trace_steps,
  message_handlert &message_handler)
{
  std::size_t random_seed = 0;

  auto consumer = [&, trace_nr = 0ull](trans_tracet trace) mutable -> void {
    namespacet ns(transition_system.symbol_table);
    auto filename = outfile_prefix + std::to_string(trace_nr + 1);
    std::ofstream out(widen_if_needed(filename));

    if(!out)
      throw ebmc_errort() << "failed to write trace to " << filename;

    messaget message(message_handler);
    show_trans_trace_vcd(trace, message, ns, out);

    trace_nr++;
  };

  random_tracest(transition_system, message_handler)(
    consumer, random_seed, number_of_traces, number_of_trace_steps);
}

/*******************************************************************\

Function: random_traces

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void random_traces(
  const transition_systemt &transition_system,
  std::function<void(trans_tracet)> consumer,
  std::size_t number_of_traces,
  std::size_t number_of_trace_steps,
  message_handlert &message_handler)
{
  std::size_t random_seed = 0;

  random_tracest(transition_system, message_handler)(
    consumer, random_seed, number_of_traces, number_of_trace_steps);
}

/*******************************************************************\

Function: random_tracest::random_bit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool random_tracest::random_bit()
{
  // We do not use std::uniform_int_distribution, as the results
  // are implementation-dependent.
  return generator() & 1;
}

/*******************************************************************\

Function: random_tracest::random_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt random_tracest::random_value(const typet &type)
{
  if(type.id() == ID_unsignedbv || type.id() == ID_signedbv)
  {
    auto width = to_bitvector_type(type).get_width();
    std::string binary_string;
    binary_string.reserve(width);
    for(std::size_t index = 0; index < width; index++)
      binary_string.push_back(random_bit() ? '1' : '0');

    return from_integer(
      binary2integer(binary_string, type.id() == ID_signedbv), type);
  }
  else if(type.id() == ID_bool)
  {
    return make_boolean_expr(random_bit());
  }
  else
    PRECONDITION(false);
}

/*******************************************************************\

Function: random_tracest::inputs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

random_tracest::symbolst random_tracest::inputs() const
{
  symbolst inputs;

  const auto &module_symbol = *transition_system.main_symbol;

  if(module_symbol.type.id() != ID_module)
    throw ebmc_errort() << "expected a module but got "
                        << module_symbol.type.id();

  const auto &ports = module_symbol.type.find(ID_ports);

  // filter out the inputs
  for(auto &port : static_cast<const exprt &>(ports).operands())
  {
    DATA_INVARIANT(port.id() == ID_symbol, "port must be a symbol");
    if(port.get_bool(ID_input) && !port.get_bool(ID_output))
    {
      symbol_exprt input_symbol(port.get(ID_identifier), port.type());
      input_symbol.add_source_location() = port.source_location();
      inputs.push_back(std::move(input_symbol));
    }
  }

  return inputs;
}

/*******************************************************************\

Function: random_tracest::state_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

random_tracest::symbolst random_tracest::state_variables() const
{
  symbolst state_variables;

  const auto &module_symbol = *transition_system.main_symbol;
  const namespacet ns(transition_system.symbol_table);

  const auto &symbol_module_map =
    transition_system.symbol_table.symbol_module_map;
  auto lower = symbol_module_map.lower_bound(module_symbol.name);
  auto upper = symbol_module_map.upper_bound(module_symbol.name);

  for(auto it = lower; it != upper; it++)
  {
    const symbolt &symbol = ns.lookup(it->second);

    if(symbol.is_state_var)
      state_variables.push_back(symbol.symbol_expr());
  }

  return state_variables;
}

/*******************************************************************\

Function: random_tracest::remove_constrained

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

random_tracest::symbolst
random_tracest::remove_constrained(const symbolst &symbols) const
{
  auto constrained_symbols = find_symbols(transition_system.trans_expr.init());

  symbolst result;
  result.reserve(symbols.size());

  // this is symbols setminus constrained_symbols
  for(auto &symbol : symbols)
    if(constrained_symbols.find(symbol) == constrained_symbols.end())
      result.push_back(symbol);

  return result;
}

/*******************************************************************\

Function: random_tracest::freeze

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void random_tracest::freeze(
  const symbolst &symbols,
  std::size_t number_of_timeframes,
  boolbvt &boolbv) const
{
  for(std::size_t i = 0; i < number_of_timeframes; i++)
  {
    for(auto &symbol : symbols)
    {
      auto symbol_in_timeframe =
        instantiate(symbol, i, number_of_timeframes, ns);
      boolbv.set_frozen(boolbv.convert_bv(symbol_in_timeframe));
    }
  }
}

/*******************************************************************\

Function: random_tracest::random_input_constraints

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::vector<exprt> random_tracest::random_input_constraints(
  decision_proceduret &solver,
  const std::vector<symbol_exprt> &inputs,
  std::size_t number_of_timeframes)
{
  std::vector<exprt> result;

  for(std::size_t i = 0; i < number_of_timeframes; i++)
  {
    for(auto &input : inputs)
    {
      auto input_in_timeframe = instantiate(input, i, number_of_timeframes, ns);
      auto constraint =
        equal_exprt(input_in_timeframe, random_value(input.type()));
      result.push_back(constraint);
    }
  }

  return result;
}

/*******************************************************************\

Function: random_tracest::random_initial_state_constraints

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::vector<exprt> random_tracest::random_initial_state_constraints(
  decision_proceduret &solver,
  const symbolst &state_variables)
{
  std::vector<exprt> result;

  for(auto &symbol : state_variables)
  {
    auto symbol_in_timeframe = instantiate(symbol, 0, 1, ns);
    auto constraint =
      equal_exprt(symbol_in_timeframe, random_value(symbol.type()));
    result.push_back(constraint);
  }

  return result;
}

/*******************************************************************\

Function: random_tracest::operator()()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void random_tracest::operator()(
  std::function<void(trans_tracet)> consumer,
  std::size_t random_seed,
  std::size_t number_of_traces,
  std::size_t number_of_trace_steps)
{
  generator.seed(random_seed);

  auto number_of_timeframes = number_of_trace_steps + 1;

  message.status() << "Passing transition system to solver" << messaget::eom;

  satcheckt satcheck{message.get_message_handler()};
  boolbvt solver(ns, satcheck, message.get_message_handler());

  ::unwind(
    transition_system.trans_expr,
    message.get_message_handler(),
    solver,
    number_of_timeframes,
    ns,
    true);

  auto inputs = this->inputs();

  if(inputs.empty())
    throw ebmc_errort() << "module does not have inputs";

  auto state_variables = this->state_variables();

  message.statistics() << "Found " << inputs.size() << " input(s) and "
                       << state_variables.size() << " state variable(s)"
                       << messaget::eom;

  auto unconstrained_state_variables = remove_constrained(state_variables);

  freeze(inputs, number_of_timeframes, solver);
  freeze(unconstrained_state_variables, 1, solver);

  message.status() << "Solving with " << solver.decision_procedure_text()
                   << messaget::eom;

  for(std::size_t trace_nr = 0; trace_nr < number_of_traces; trace_nr++)
  {
    auto input_constraints =
      random_input_constraints(solver, inputs, number_of_timeframes);

    auto initial_state_constraints =
      random_initial_state_constraints(solver, unconstrained_state_variables);

    auto merged =
      merge_constraints(input_constraints, initial_state_constraints);

    solver.push(merged);
    auto dec_result = solver();
    solver.pop();

    switch(dec_result)
    {
    case decision_proceduret::resultt::D_SATISFIABLE:
    {
      auto trace = compute_trans_trace(
        solver, number_of_timeframes, ns, transition_system.main_symbol->name);
      consumer(std::move(trace));
    }
    break;

    case decision_proceduret::resultt::D_UNSATISFIABLE:
      break;

    case decision_proceduret::resultt::D_ERROR:
      throw ebmc_errort() << "Error from decision procedure";

    default:
      throw ebmc_errort() << "Unexpected result from decision procedure";
    }
  }
}
