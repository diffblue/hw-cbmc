/*******************************************************************\

Module: Neural Engine

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "neural.h"

#if 0
#  include <util/arith_tools.h>
#  include <util/bitvector_expr.h>
#  include <util/bitvector_types.h>
#  include <util/format_expr.h>
#  include <util/string2int.h>

#  include <solvers/flattening/boolbv.h>
#  include <solvers/sat/satcheck.h>
#  include <temporal-logic/temporal_expr.h>
#  include <verilog/sva_expr.h>

#  include "live_signal.h"
#  include "random_traces.h"
#  include "ranking_function.h"
#  include "ranking_net.h"
#  include "report_results.h"
#  include "waveform.h"
#endif

#include <temporal-logic/ltl.h>
#include <temporal-logic/ltl_to_buechi.h>
#include <temporal-logic/temporal_logic.h>

#include "ebmc_error.h"
#include "ebmc_solver_factory.h"

/*******************************************************************\

   Class: neural_enginet

 Purpose:

\*******************************************************************/

class neural_enginet
{
public:
  neural_enginet(
    const cmdlinet &_cmdline,
    transition_systemt &_transition_system,
    ebmc_propertiest &_properties,
    message_handlert &_message_handler)
    : cmdline(_cmdline),
      transition_system(_transition_system),
      properties(_properties),
      message_handler(_message_handler),
      solver_factory(ebmc_solver_factory(_cmdline))
  {
  }

  property_checker_resultt operator()();

protected:
  const cmdlinet &cmdline;
  transition_systemt &transition_system;
  ebmc_propertiest &properties; // this is a copy
  message_handlert &message_handler;
  ebmc_solver_factoryt solver_factory;

#if 0
  std::vector<symbol_exprt> state_variables;
  using state_variable_mapt = std::unordered_map<exprt, std::size_t, irep_hash>;
  state_variable_mapt state_variable_map;

  using propertyt = ebmc_propertiest::propertyt;

  using tracest = std::list<trans_tracet>;
  tracest traces;

  // trace state to state vector
  tuple_exprt to_vector(const trans_tracet::statet &, const typet &) const;

  exprt
  net_to_expression(const ranking_nett &, const decision_proceduret &) const;

  int show_traces();
  void validate_properties();
  void set_live_signal(const propertyt &, const exprt &);
  void sample();
  exprt guess(propertyt &);
  void minimize(decision_proceduret &, const exprt &objective);
  tvt verify(propertyt &, const exprt &candidate);
#endif
};

static ebmc_propertiest::propertyt &find_property(ebmc_propertiest &properties)
{
  // we only do one property
  std::vector<ebmc_propertiest::propertyt *> ptrs;

  for(auto &property : properties.properties)
    if(property.is_unknown())
      ptrs.push_back(&property);

  if(ptrs.empty())
    throw ebmc_errort() << "no property";

  if(ptrs.size() >= 2)
    throw ebmc_errort() << "The neural engine expects one property";

  return *ptrs.front();
}

property_checker_resultt neural_enginet::operator()()
{
  auto &property = find_property(properties);

  // This is for LTL and some fragment of SVA only.
  if(
    !is_LTL(property.normalized_expr) &&
    !is_Buechi_SVA(property.normalized_expr))
  {
    throw ebmc_errort{}
      << "The neural engine works on omega-regular properties only";
  }

  messaget message{message_handler};
  message.debug() << "Translating " << property.description << " to Buechi"
                  << messaget::eom;

  // make the automaton for the negation of the property
  auto buechi =
    ltl_to_buechi(not_exprt{property.normalized_expr}, message_handler);

  return property_checker_resultt{std::move(properties)};
}

#if 0
static std::unordered_map<exprt, std::size_t, irep_hash>
to_map(const std::vector<symbol_exprt> &state_variables)
{
  std::unordered_map<exprt, std::size_t, irep_hash> result;
  for(auto &v : state_variables)
    result.emplace(v, result.size());
  return result;
}

int solver_neural_livenesst::operator()()
{
  if(cmdline.isset("show-traces"))
    return show_traces();

  state_variables = transition_system.state_variables();
  state_variable_map = to_map(state_variables);

  // Save the transition system expression,
  // to add the constraint for the 'live' signal.
  const auto original_trans_expr = transition_system.main_symbol->value;

  // We do everything per property.
  for(auto &property : properties.properties)
  {
    if(property.is_disabled())
      continue;

    // Set the liveness signal for the property.
    set_live_signal(property, original_trans_expr);

    // Now sample some traces.
    sample();

    // Now do a guess-and-verify loop.
    while(true)
    {
      const auto candidate = guess(property);

      if(verify(property, candidate).is_true())
        break; // done, property holds

      const namespacet ns(transition_system.symbol_table);
      show_waveform(property.witness_trace.value(), ns);

      // record the counterexample
      traces.push_back(property.witness_trace.value());
    }
  }
}

int solver_neural_livenesst::show_traces()
{
  transition_system =
    get_transition_system(cmdline, message.get_message_handler());

  properties = ebmc_propertiest::from_command_line(
    cmdline, transition_system, message.get_message_handler());

  validate_properties();

  const auto original_trans_expr = transition_system.main_symbol->value;

  for(auto &property : properties.properties)
  {
    if(property.is_disabled())
      continue;

    set_live_signal(property, original_trans_expr);

    sample();

    const namespacet ns(transition_system.symbol_table);

    for(const auto &trace : traces)
      show_trans_trace_numbered(trace, message, ns, std::cout);
  }

  return 0;
}

void solver_neural_livenesst::validate_properties()
{

  for(auto &property : properties.properties)
  {
    if(property.is_disabled())
    {
      // ignore
    }
    else if(property.normalized_expr.id() == ID_AF)
    {
      // ok
    }
    else if(
      property.normalized_expr.id() == ID_sva_always &&
      to_sva_always_expr(property.normalized_expr).op().id() ==
        ID_sva_s_eventually)
    {
      // ok
    }
    else
    {
      throw ebmc_errort()
        << "unsupported property - only SVA s_eventually or AF implemented";
    }
  }
}

void solver_neural_livenesst::set_live_signal(
  const ebmc_propertiest::propertyt &property,
  const exprt &original_trans_expr)
{
  // restore the original transition system
  auto main_symbol_writeable = transition_system.symbol_table.get_writeable(
    transition_system.main_symbol->name);
  main_symbol_writeable->value = original_trans_expr; // copy
  ::set_live_signal(transition_system, property.normalized_expr);
}

void solver_neural_livenesst::sample()
{
  const auto number_of_traces = [this]() -> std::size_t {
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

  const std::size_t number_of_trace_steps = [this]() -> std::size_t {
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

  message.status() << "Sampling " << number_of_traces << " traces with "
                   << number_of_trace_steps << " steps" << messaget::eom;

  auto trace_consumer = [&](trans_tracet trace) {
    traces.push_back(std::move(trace));
  };

  random_traces(
    transition_system,
    trace_consumer,
    number_of_traces,
    number_of_trace_steps,
    message.get_message_handler());
}

static bool is_live(const trans_tracet::statet &state)
{
  for(auto &assignment : state.assignments)
  {
    auto &lhs = assignment.lhs;
    if(
      lhs.id() == ID_symbol &&
      to_symbol_expr(lhs).get_identifier() == "nuterm::live")
      return assignment.rhs.is_true();
  }

  throw ebmc_errort() << "liveness signal not found";
}

static exprt loss_constraint(tuple_exprt curr, tuple_exprt next)
{
  PRECONDITION(curr.operands().size() == next.operands().size());

  // The ranking needs to decrease from 'curr' to 'next'.
  auto &curr_val = curr.operands()[0];
  auto &next_val = next.operands()[0];
  return less_than_exprt{next_val, curr_val};
}

tuple_exprt solver_neural_livenesst::to_vector(
  const trans_tracet::statet &state,
  const typet &type) const
{
  tuple_exprt::operandst result;
  result.resize(state_variable_map.size(), from_integer(0, type));

  for(auto &assignment : state.assignments)
  {
    auto s_it = state_variable_map.find(assignment.lhs);
    if(s_it != state_variable_map.end())
      if(assignment.rhs.is_constant())
        result[s_it->second] =
          typecast_exprt::conditional_cast(assignment.rhs, type);
  }

  return tuple_exprt{std::move(result)};
}

static exprt objective(const ranking_nett &net)
{
  // return from_integer(0, signedbv_typet{32});

  exprt::operandst summands;

  for(auto &neuron : net.fc1.neurons)
  {
    for(auto &weight : neuron.weights)
      summands.push_back(abs_exprt{weight});

    // summands.push_back(abs_exprt{neuron.bias});
  }

  DATA_INVARIANT(!summands.empty(), "must have neuron");
  auto type = summands[0].type();

  return plus_exprt{std::move(summands), std::move(type)};
}

void solver_neural_livenesst::minimize(
  decision_proceduret &solver,
  const exprt &objective)
{
  exprt objective_value = nil_exprt();

  std::size_t iteration = 0;
  while(true)
  {
    iteration++;
    message.status() << "iteration " << iteration << messaget::eom;

    // we want a better solution
    auto constraint = objective_value.is_nil()
                        ? static_cast<exprt>(true_exprt())
                        : less_than_exprt{objective, objective_value};

    auto dec_result = solver(constraint);

    switch(dec_result)
    {
    case decision_proceduret::resultt::D_SATISFIABLE:
      objective_value = solver.get(objective);
      message.status() << "objective: " << format(objective_value)
                       << messaget::eom;
      break;

    case decision_proceduret::resultt::D_UNSATISFIABLE:
      if(objective_value.is_nil())
      {
        // no ranking function possible
        throw ebmc_errort()
          << "architecture does not allow ranking function, giving up";
      }

      message.status() << "found optimal assignment" << messaget::eom;

      // go back to previous, to get satisfying assignment
      solver(equal_exprt{objective, objective_value});
      return;

    case decision_proceduret::resultt::D_ERROR:
      throw ebmc_errort() << "Error from decision procedure";

    default:
      throw ebmc_errort() << "Unexpected result from decision procedure";
    }
  }
}

static void bits_constraint(
  const exprt &expr,
  std::size_t bits,
  decision_proceduret &solver)
{
  PRECONDITION(bits != 0);

  auto expr_bits = to_bitvector_type(expr.type()).get_width();

  if(expr_bits <= bits)
    return; // nothing to do

  // signed encoding
  auto top_bit = extractbit_exprt{expr, expr_bits - 1};

  for(std::size_t i = bits; i < expr_bits - 1; i++)
    solver << equal_exprt{top_bit, extractbit_exprt{expr, i}};
}

exprt solver_neural_livenesst::net_to_expression(
  const ranking_nett &net,
  const decision_proceduret &solver) const
{
  // get the weights
  for(std::size_t i = 0; i < state_variables.size(); i++)
  {
    auto weight_value = solver.get(net.fc1.neurons[0].weights[i]);
    std::cout << "weight: " << format(state_variables[i]) << " = " 
              << format(weight_value) << '\n';
  }

  // get the bias
  auto &bias = net.fc1.neurons[0].bias;
  std::cout << "bias: " << format(bias) << " = " << format(solver.get(bias))
            << '\n';

  exprt::operandst summands;

  for(std::size_t i = 0; i < state_variables.size(); i++)
  {
    auto weight_value = solver.get(net.fc1.neurons[0].weights[i]);
    if(!weight_value.is_zero())
      summands.push_back(mult_exprt{
        weight_value,
        typecast_exprt::conditional_cast(
          state_variables[i], weight_value.type())});
  }

  if(!solver.get(bias).is_zero())
    summands.push_back(solver.get(bias));

  if(summands.empty())
    throw ebmc_errort() << "no weights";

  exprt fc1;

  if(summands.size() == 1)
    fc1 = summands.front();
  else
  {
    auto type = summands.front().type();
    fc1 = plus_exprt{std::move(summands), std::move(type)};
  }

  return wrap_around(fc1);
}

exprt solver_neural_livenesst::guess(propertyt &property)
{
  message.status() << "Fitting a ranking function" << messaget::eom;

  const namespacet ns(transition_system.symbol_table);
  satcheckt satcheck{message.get_message_handler()};
  boolbvt solver(ns, satcheck, message.get_message_handler());
  //auto solver_container = solver_factory(ns, message.get_message_handler());
  //auto &solver = solver_container.decision_procedure();

  // set up net
  auto net_type = signedbv_typet{40};
  std::size_t dimension = 2;
  auto net = ranking_nett{state_variable_map.size(), dimension, net_type};

  // form a batch
  std::size_t transitions = 0;

  for(const auto &trace : traces)
  {
    for(std::size_t i = 1; i < trace.states.size(); i++)
    {
      auto &curr = trace.states[i - 1];
      auto &next = trace.states[i];

      if(is_live(curr) || is_live(next))
        continue;

      auto prediction_curr = net.forward(to_vector(curr, net_type));
      auto prediction_next = net.forward(to_vector(next, net_type));

      // loss must be zero
      solver << loss_constraint(
        std::move(prediction_curr), std::move(prediction_next));

      transitions++;
    }
  }

  message.status() << "Batch with " << transitions << " transition(s)"
                   << messaget::eom;

  // constraints on parameters
  for(auto &weight : net.fc1.neurons[0].weights)
    bits_constraint(weight, 2, solver);

  // get the bias
  bits_constraint(net.fc1.neurons[0].bias, 35, solver);

  // minimize
  auto objective = ::objective(net);
  message.status() << format(objective) << messaget::eom;
  const auto objective_symbol =
    symbol_exprt{"nuterm::objective", objective.type()};
  solver << equal_exprt{objective_symbol, std::move(objective)};
  solver.set_frozen(solver.convert_bv(objective_symbol));
  minimize(solver, objective_symbol);

  // read off the candidate
  exprt candidate = net_to_expression(net, solver);

  message.status() << "candidate: " << messaget::green << format(candidate)
                   << messaget::reset << messaget::eom;

  return candidate;
}

tvt solver_neural_livenesst::verify(
  ebmc_propertiest::propertyt &property,
  const exprt &candidate)
{
  message.status() << "Checking the candidate ranking function"
                   << messaget::eom;

  auto result = is_ranking_function(
    transition_system,
    property.normalized_expr,
    candidate,
    solver_factory,
    message.get_message_handler());

  property.witness_trace = std::move(result.second);

  if(result.first.is_true())
    property.proved();
  else
    property.inconclusive();

  return result.first;
}
#endif

property_checker_resultt neural(
  const cmdlinet &cmdline,
  transition_systemt &transition_system,
  ebmc_propertiest &properties,
  message_handlert &message_handler)
{
  neural_enginet neural_engine{
    cmdline, transition_system, properties, message_handler};
  return neural_engine();
}
