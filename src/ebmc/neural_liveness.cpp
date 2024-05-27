/*******************************************************************\

Module: Neural Liveness

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "neural_liveness.h"

#include <util/prefix.h>
#include <util/run.h>
#include <util/string2int.h>
#include <util/tempdir.h>
#include <util/tempfile.h>
#include <util/unicode.h>

#include <temporal-logic/temporal_expr.h>
#include <verilog/sva_expr.h>

#include "ebmc_error.h"
#include "ebmc_solver_factory.h"
#include "live_signal.h"
#include "random_traces.h"
#include "ranking_function.h"
#include "report_results.h"
#include "waveform.h"

#include <fstream>
#include <iostream>

/*******************************************************************\

   Class: neural_livenesst

 Purpose:

\*******************************************************************/

class neural_livenesst
{
public:
  neural_livenesst(const cmdlinet &_cmdline, message_handlert &_message_handler)
    : cmdline(_cmdline),
      message(_message_handler),
      solver_factory(ebmc_solver_factory(_cmdline))
  {
  }

  int operator()();

protected:
  const cmdlinet &cmdline;
  messaget message;
  ebmc_solver_factoryt solver_factory;
  transition_systemt transition_system;
  ebmc_propertiest properties;

  int show_traces();
  void validate_properties();
  void set_live_signal(const ebmc_propertiest::propertyt &, const exprt &);
  void sample(std::function<void(trans_tracet)>);
  std::function<void(trans_tracet)> dump_vcd_files(temp_dirt &);
  exprt guess(ebmc_propertiest::propertyt &, const temp_dirt &);
  tvt verify(ebmc_propertiest::propertyt &, const exprt &candidate);
};

int neural_livenesst::operator()()
{
  if(cmdline.isset("show-traces"))
    return show_traces();

  if(!cmdline.isset("neural-engine"))
    throw ebmc_errort() << "give a neural engine";

  transition_system =
    get_transition_system(cmdline, message.get_message_handler());

  // Get the properties
  properties = ebmc_propertiest::from_command_line(
    cmdline, transition_system, message.get_message_handler());

  // Establish that the given properties are appropriate for
  // neural liveness.
  validate_properties();

  auto solver_factory = ebmc_solver_factory(cmdline);

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
    // Store the traces in a set of files, one per
    // trace, which are then read by the neural fitting procedure.
    temp_dirt temp_dir("ebmc-neural.XXXXXXXX");
    const auto trace_files_prefix = temp_dir("trace.");
    sample(dump_vcd_files(temp_dir));

    // Now do a guess-and-verify loop.
    while(true)
    {
      const auto candidate = guess(property, temp_dir);

      if(verify(property, candidate).is_true())
        break;
    }
  }

  // report outcomes
  const namespacet ns(transition_system.symbol_table);
  report_results(cmdline, properties, ns, message.get_message_handler());
  return properties.exit_code();
}

int neural_livenesst::show_traces()
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

    sample([&](trans_tracet trace) {
      namespacet ns(transition_system.symbol_table);
      show_trans_trace_numbered(trace, message, ns, std::cout);
    });
  }

  return 0;
}

void neural_livenesst::validate_properties()
{
  if(properties.properties.empty())
    throw ebmc_errort() << "no properties";

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

void neural_livenesst::set_live_signal(
  const ebmc_propertiest::propertyt &property,
  const exprt &original_trans_expr)
{
  // restore the original transition system
  auto main_symbol_writeable = transition_system.symbol_table.get_writeable(
    transition_system.main_symbol->name);
  main_symbol_writeable->value = original_trans_expr; // copy
  ::set_live_signal(transition_system, property.normalized_expr);
}

std::function<void(trans_tracet)>
neural_livenesst::dump_vcd_files(temp_dirt &temp_dir)
{
  const auto outfile_prefix = temp_dir("trace.");
  return
    [&, trace_nr = 0ull, outfile_prefix](trans_tracet trace) mutable -> void {
      namespacet ns(transition_system.symbol_table);
      auto filename = outfile_prefix + std::to_string(trace_nr + 1);
      std::ofstream out(widen_if_needed(filename));

      if(!out)
        throw ebmc_errort() << "failed to write trace to " << filename;

      message.progress() << "*** Writing " << filename << messaget::eom;
      show_trans_trace_vcd(trace, message, ns, out);
    };
}

void neural_livenesst::sample(std::function<void(trans_tracet)> trace_consumer)
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
      return 100; // default
  }();

  const std::size_t number_of_trace_steps = [this]() -> std::size_t
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

  message.status() << "Sampling " << number_of_traces << " traces with "
                   << number_of_trace_steps << " steps" << messaget::eom;

  random_traces(
    transition_system,
    trace_consumer,
    number_of_traces,
    number_of_trace_steps,
    solver_factory,
    message.get_message_handler());
}

exprt neural_livenesst::guess(
  ebmc_propertiest::propertyt &property,
  const temp_dirt &temp_dir)
{
  message.status() << "Fitting a ranking function" << messaget::eom;

  const auto engine = cmdline.get_value("neural-engine");
  temporary_filet engine_output("ebmc-neural", "txt");
  const auto cmd = engine + " " + temp_dir.path + " | tee " + engine_output();

  auto shell = "/bin/sh";
  auto result = run(shell, {shell, "-c", cmd});

  if(result != 0)
    throw ebmc_errort() << "neural engine exited with " << result
                        << ", aborting";

  // find "Candidate: " in the output
  std::ifstream in(engine_output());
  if(!in)
    throw ebmc_errort() << "failed to open " << engine_output();

  std::string prefix = "Candidate: ";
  std::string line;
  while(std::getline(in, line))
  {
    if(has_prefix(line, prefix))
    {
      auto candidate = line.substr(prefix.size());
      message.status() << "Obtained candidate " << candidate << messaget::eom;
      return parse_ranking_function(
        candidate, transition_system, message.get_message_handler());
    }
  }

  throw ebmc_errort() << "failed to find candidate in neural engine output";
}

tvt neural_livenesst::verify(
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

int do_neural_liveness(
  const cmdlinet &cmdline,
  ui_message_handlert &ui_message_handler)
{
  return neural_livenesst(cmdline, ui_message_handler)();
}
