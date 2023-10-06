/*******************************************************************\

Module: Random Trace Generation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "random_traces.h"

#include "ebmc_base.h"

#include <trans-word-level/instantiate_word_level.h>
#include <trans-word-level/property.h>
#include <trans-word-level/trans_trace_word_level.h>
#include <trans-word-level/unwind.h>

#include <solvers/flattening/boolbv.h>
#include <solvers/sat/satcheck.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/console.h>
#include <util/expr_util.h>
#include <util/string2int.h>

#include <algorithm>
#include <random>

/*******************************************************************\

   Class: random_tracest

 Purpose:

\*******************************************************************/

class random_tracest : public ebmc_baset
{
public:
  random_tracest(
    const cmdlinet &_cmdline,
    ui_message_handlert &_ui_message_handler)
    : ebmc_baset(_cmdline, _ui_message_handler), ns{symbol_table}
  {
  }

  int operator()();

protected:
  namespacet ns;

  std::vector<exprt> random_input_constraints(
    decision_proceduret &,
    const std::vector<symbol_exprt> &inputs,
    size_t number_of_timeframes);

  constant_exprt random_value(const typet &);

  std::vector<symbol_exprt> inputs() const;

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

int random_traces(
  const cmdlinet &cmdline,
  ui_message_handlert &ui_message_handler)
{
  return random_tracest(cmdline, ui_message_handler)();
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

std::vector<symbol_exprt> random_tracest::inputs() const
{
  std::vector<symbol_exprt> inputs;
  const symbol_tablet &symbol_table = ns.get_symbol_table();

  auto module_identifier = main_symbol->name;
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

int random_tracest::operator()()
{
  auto number_of_traces_opt =
    string2optional_size_t(cmdline.get_value("random-traces"));

  if(!number_of_traces_opt.has_value())
  {
    error() << "failed to parse number of traces" << eom;
    return 1;
  }

  if(cmdline.isset("random-seed"))
  {
    auto random_seed_opt =
      string2optional_size_t(cmdline.get_value("random-seed"));

    if(!random_seed_opt.has_value())
    {
      error() << "failed to parse random seed" << eom;
      return 1;
    }

    generator.seed(random_seed_opt.value());
  }
  else
    generator.seed(0);

  if(get_bound())
    return 1;

  auto number_of_timeframes = bound + 1;

  int result = get_model();
  if(result != -1)
    return result;

  CHECK_RETURN(trans_expr.has_value());

  status() << "Passing transition system to solver" << eom;

  satcheckt satcheck{*message_handler};
  boolbvt solver(ns, satcheck, *message_handler);

  ::unwind(
    *trans_expr, *message_handler, solver, number_of_timeframes, ns, true);

  auto inputs = this->inputs();

  statistics() << "Found " << inputs.size() << " input(s)" << eom;

  status() << "Solving with " << solver.decision_procedure_text() << eom;

  for(std::size_t trace_nr = 0; trace_nr < number_of_traces_opt.value();
      trace_nr++)
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
        solver, number_of_timeframes, ns, main_symbol->name);
      if(cmdline.isset("vcd"))
      {
        auto filename =
          cmdline.get_value("vcd") + "." + std::to_string(trace_nr + 1);
        std::ofstream out(filename);
        if(!out)
        {
          error() << "failed to write trace to " << filename << eom;
          return 1;
        }

        consolet::out() << "*** Writing " << filename << '\n';

        show_trans_trace_vcd(trace, *this, ns, out);
      }
      else
      {
        consolet::out() << "*** Trace " << (trace_nr + 1) << '\n';
        show_trans_trace(
          trace,
          *this,
          ns,
          static_cast<ui_message_handlert *>(message_handler)->get_ui());
      }
    }
    break;

    case decision_proceduret::resultt::D_UNSATISFIABLE:
      break;

    case decision_proceduret::resultt::D_ERROR:
      error() << "Error from decision procedure" << messaget::eom;
      return 2;

    default:
      error() << "Unexpected result from decision procedure" << messaget::eom;
      return 1;
    }
  }

  return 0;
}
