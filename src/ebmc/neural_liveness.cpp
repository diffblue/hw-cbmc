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

#include "ebmc_error.h"
#include "random_traces.h"
#include "ranking_function.h"
#include "report_results.h"

#include <fstream>

/*******************************************************************\

   Class: neural_livenesst

 Purpose:

\*******************************************************************/

class neural_livenesst
{
public:
  neural_livenesst(const cmdlinet &_cmdline, message_handlert &_message_handler)
    : cmdline(_cmdline), message(_message_handler)
  {
  }

  int operator()();

protected:
  const cmdlinet &cmdline;
  messaget message;
  transition_systemt transition_system;
  ebmc_propertiest properties;

  void validate_properties();
  void sample(temp_dirt &);
  exprt guess(ebmc_propertiest::propertyt &, const temp_dirt &);
  tvt verify(ebmc_propertiest::propertyt &, const exprt &candidate);
};

int neural_livenesst::operator()()
{
  if(!cmdline.isset("neural-engine"))
    throw ebmc_errort() << "give a neural engine";

  int result = get_transition_system(
    cmdline, message.get_message_handler(), transition_system);
  if(result != -1)
    return result;

  // Get the properties
  properties = ebmc_propertiest::from_command_line(
    cmdline, transition_system, message.get_message_handler());

  // Establish that the given properties are appropriate for
  // neural liveness.
  validate_properties();

  // Now sample some traces.  These get stored in a set of files, one per
  // trace, and are then read by the neural fitting procedure.
  temp_dirt temp_dir("ebmc-neural.XXXXXXXX");
  sample(temp_dir);

  // We now do a guess-verify loop, per property.
  for(auto &property : properties.properties)
  {
    if(property.is_disabled())
      continue;

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
    else if(property.expr.id() == ID_AF)
    {
      // ok
    }
    else if(
      property.expr.id() == ID_sva_always &&
      to_unary_expr(property.expr).op().id() == ID_sva_eventually)
    {
      // ok
    }
    else
    {
      throw ebmc_errort()
        << "unsupported property - only SVA eventually or AF implemented";
    }
  }
}

void neural_livenesst::sample(temp_dirt &temp_dir)
{
  const auto trace_files_prefix = temp_dir("trace.");

  const auto number_of_traces = [this]() -> std::size_t
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
    trace_files_prefix,
    number_of_traces,
    number_of_trace_steps,
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
    transition_system, property.expr, candidate, message.get_message_handler());

  if(result.is_true())
    property.make_success();

  return result;
}

int do_neural_liveness(
  const cmdlinet &cmdline,
  ui_message_handlert &ui_message_handler)
{
  return neural_livenesst(cmdline, ui_message_handler)();
}
