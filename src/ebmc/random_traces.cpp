/*******************************************************************\

Module: Random Trace Generation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "random_traces.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/console.h>
#include <util/expr_util.h>
#include <util/string2int.h>
#include <util/unicode.h>

#include <solvers/flattening/boolbv.h>
#include <solvers/sat/satcheck.h>
#include <trans-word-level/instantiate_word_level.h>
#include <trans-word-level/property.h>
#include <trans-word-level/trans_trace_word_level.h>
#include <trans-word-level/unwind.h>

#include "ebmc_base.h"
#include "ebmc_error.h"

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
    const optionalt<std::string> &outfile_prefix,
    std::size_t random_seed,
    std::size_t number_of_traces,
    std::size_t number_of_trace_steps);

protected:
  const transition_systemt &transition_system;
  const namespacet ns;
  messaget message;

  using inputst = std::vector<symbol_exprt>;

  std::vector<exprt> random_input_constraints(
    decision_proceduret &,
    const inputst &,
    size_t number_of_timeframes);

  constant_exprt random_value(const typet &);

  inputst inputs() const;

  void freeze_inputs(
    const inputst &,
    std::size_t number_of_timeframes,
    boolbvt &) const;

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
    if(cmdline.isset("number-of-traces"))
    {
      auto number_of_traces_opt =
        string2optional_size_t(cmdline.get_value("number-of-traces"));

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

  const auto outfile_prefix = [&cmdline]() -> optionalt<std::string>
  {
    if(cmdline.isset("vcd"))
      return cmdline.get_value("vcd") + ".";
    else
      return {};
  }();

  transition_systemt transition_system =
    get_transition_system(cmdline, message_handler);

  random_tracest(transition_system, message_handler)(
    outfile_prefix, random_seed, number_of_traces, number_of_trace_steps);

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
  random_tracest(transition_system, message_handler)(
    outfile_prefix, random_seed, number_of_traces, number_of_trace_steps);
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

random_tracest::inputst random_tracest::inputs() const
{
  inputst inputs;
  const symbol_tablet &symbol_table = ns.get_symbol_table();

  auto module_identifier = transition_system.main_symbol->name;
  auto lower = symbol_table.symbol_module_map.lower_bound(module_identifier);
  auto upper = symbol_table.symbol_module_map.upper_bound(module_identifier);

  // We need a deterministic ordering of the inputs that's
  // portable accross implementations. We use irep_idt::compare.
  std::vector<irep_idt> input_identifiers;

  for(auto it = lower; it != upper; it++)
  {
    const symbolt &symbol = ns.lookup(it->second);

    if(symbol.is_input)
      input_identifiers.push_back(symbol.name);
  }

  // sort by identifier
  std::sort(
    input_identifiers.begin(),
    input_identifiers.end(),
    [](const irep_idt &a, const irep_idt &b) { return a.compare(b) < 0; });

  // turn into symbol_exprt
  for(auto identifier : input_identifiers)
    inputs.push_back(ns.lookup(identifier).symbol_expr());

  return inputs;
}

/*******************************************************************\

Function: random_tracest::freeze_inputs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void random_tracest::freeze_inputs(
  const inputst &inputs,
  std::size_t number_of_timeframes,
  boolbvt &boolbv) const
{
  for(std::size_t i = 0; i < number_of_timeframes; i++)
  {
    for(auto &input : inputs)
    {
      auto input_in_timeframe = instantiate(input, i, number_of_timeframes, ns);
      boolbv.set_frozen(boolbv.convert_bv(input_in_timeframe));
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
      result.push_back(solver.handle(constraint));
    }
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
  const optionalt<std::string> &outfile_prefix,
  std::size_t random_seed,
  std::size_t number_of_traces,
  std::size_t number_of_trace_steps)
{
  generator.seed(random_seed);

  auto number_of_timeframes = number_of_trace_steps + 1;

  PRECONDITION(transition_system.trans_expr.has_value());

  message.status() << "Passing transition system to solver" << messaget::eom;

  satcheckt satcheck{message.get_message_handler()};
  boolbvt solver(ns, satcheck, message.get_message_handler());

  ::unwind(
    *transition_system.trans_expr,
    message.get_message_handler(),
    solver,
    number_of_timeframes,
    ns,
    true);

  auto inputs = this->inputs();

  message.statistics() << "Found " << inputs.size() << " input(s)"
                       << messaget::eom;

  freeze_inputs(inputs, number_of_timeframes, solver);

  message.status() << "Solving with " << solver.decision_procedure_text()
                   << messaget::eom;

  for(std::size_t trace_nr = 0; trace_nr < number_of_traces; trace_nr++)
  {
    auto input_constraints =
      random_input_constraints(solver, inputs, number_of_timeframes);

    solver.push(input_constraints);
    auto dec_result = solver();
    solver.pop();

    switch(dec_result)
    {
    case decision_proceduret::resultt::D_SATISFIABLE:
    {
      auto trace = compute_trans_trace(
        solver, number_of_timeframes, ns, transition_system.main_symbol->name);
      if(outfile_prefix.has_value())
      {
        auto filename = outfile_prefix.value() + std::to_string(trace_nr + 1);
        std::ofstream out(widen_if_needed(filename));

        if(!out)
          throw ebmc_errort() << "failed to write trace to " << filename;

        consolet::out() << "*** Writing " << filename << '\n';

        show_trans_trace_vcd(trace, message, ns, out);
      }
      else
      {
        consolet::out() << "*** Trace " << (trace_nr + 1) << '\n';
        show_trans_trace(trace, message, ns, consolet::out());
      }
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
