/*******************************************************************\

Module: Traces to Tensors

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "traces_to_tensors.h"

double vcd_to_value(const std::string &src)
{
  // VCD gives binary values
  auto integer = std::stoull(src, nullptr, 2);
  //std::cout << "VALUE " << src << " -> " << double(integer) << "\n";
  return integer;
}

torch::Tensor state_to_tensor(
  const state_variablest &state_variables,
  const vcdt::statet &state)
{
  std::vector<double> data;
  data.resize(state_variables.size(), 0);
  for(auto &[id, var] : state_variables)
  {
    if(var.reference == "clk")
      continue;
    auto v_it = state.changes.find(id);
    if(v_it != state.changes.end())
      data[var.index] = vcd_to_value(v_it->second);
  }

  return torch::tensor(data, torch::kFloat64);
}

bool is_live_state(
  const std::string &liveness_signal,
  const vcdt::statet &state)
{
  auto value_it = state.changes.find(liveness_signal);
  if(value_it == state.changes.end())
  {
    std::cerr << "state without liveness signal" << '\n';
    abort();
  }
  return vcd_to_value(value_it->second) != 0;
}

std::vector<batcht> traces_to_tensors(
  const state_variablest &state_variables,
  const std::string &liveness_signal,
  const tracest &traces,
  std::size_t batch_size)
{
  // all batches
  std::vector<batcht> result;

  // current batch
  std::vector<torch::Tensor> batch_curr, batch_next;
  batch_curr.reserve(batch_size);
  batch_next.reserve(batch_size);

  for(auto &trace : traces)
  {
    const auto full_trace = trace.full_trace();

    for(std::size_t t = 1; t < full_trace.size(); t++)
    {
      auto &current = full_trace[t - 1];
      auto &next = full_trace[t];

      // We must discard transitions in/out of 'live' states.
      // There is no need for the ranking function to decrease
      // on such transitions.
      if(
        !is_live_state(liveness_signal, current) &&
        !is_live_state(liveness_signal, next))
      {
        // std::cout << "\n" << current << "---->\n" << next;
        auto tensor_curr = state_to_tensor(state_variables, current);
        auto tensor_next = state_to_tensor(state_variables, next);
        assert(tensor_curr.size(0) == state_variables.size());
        assert(tensor_next.size(0) == state_variables.size());

        // add to batch
        batch_curr.push_back(std::move(tensor_curr));
        batch_next.push_back(std::move(tensor_next));

        // full batch?
        if(batch_curr.size() == batch_size)
        {
          result.emplace_back(batch_curr, batch_next);
          batch_curr.resize(0);
          batch_next.resize(0);
          batch_curr.reserve(batch_size);
          batch_next.reserve(batch_size);
        }
      }
    }
  }

  // incomplete batch?
  if(!batch_curr.empty())
  {
    result.emplace_back(batch_curr, batch_next);
  }

  return result;
}
