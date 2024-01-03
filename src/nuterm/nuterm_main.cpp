/*******************************************************************\

Module: nuterm main

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "training.h"
#include "vcd_parser.h"

#include <algorithm>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <list>
#include <string>

using tracest = std::list<vcdt>;

tracest read_traces(const std::string &path)
{
  std::vector<std::string> file_names;

  for(const auto &entry : std::filesystem::directory_iterator(path))
    file_names.push_back(entry.path());

  // sort to get a fixed ordering
  std::sort(file_names.begin(), file_names.end());

  tracest traces;

  for(const auto &entry : file_names)
  {
    std::cout << "Reading " << entry << '\n';
    std::ifstream in(entry);
    traces.push_back(vcd_parser(in));
  }

  return traces;
}

std::size_t number_of_transitions(const tracest &traces)
{
  std::size_t result = 0;

  for(auto &trace : traces)
    result += trace.states.empty() ? 0 : trace.states.size() - 1;

  return result;
}

using state_variablest = std::map<std::string, std::size_t>;

state_variablest state_variables(const tracest &traces)
{
  // number all identifiers
  state_variablest identifiers;
  for(auto &trace : traces)
    for(auto &state : trace.states)
      for(auto &value_change : state.changes)
        identifiers.emplace(value_change.first, identifiers.size());

  return identifiers;
}

#include <iostream>

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
  for(auto &var : state_variables)
  {
    auto v_it = state.changes.find(var.first);
    if(v_it != state.changes.end())
      data[var.second] = vcd_to_value(v_it->second);
  }

  return torch::tensor(data, torch::kFloat64);
}

torch::Tensor state_pair_to_tensor(
  const state_variablest &state_variables,
  const vcdt::statet &current,
  const vcdt::statet &next)
{
  // We make a tensor that has dimensions 2 x |V|.
  // The '2' allows for current and next state.
  auto tensor_current = state_to_tensor(state_variables, current);
  auto tensor_next = state_to_tensor(state_variables, next);
  auto tensor_pair = torch::stack({tensor_current, tensor_next}, 0);
  //  std::cout << "P: " << tensor_pair << "\n" << std::flush;
  return std::move(tensor_pair);
}

std::vector<torch::Tensor> traces_to_tensors(
  const state_variablest &state_variables,
  const tracest &traces)
{
  auto t = number_of_transitions(traces);

  std::vector<torch::Tensor> result;
  result.reserve(t);

  for(auto &trace : traces)
  {
    const auto full_trace = trace.full_trace();
    for(std::size_t t = 1; t < full_trace.size(); t++)
    {
      auto &current = full_trace[t - 1];
      auto &next = full_trace[t];
      auto tensor = state_pair_to_tensor(state_variables, current, next);
      result.push_back(std::move(tensor));
    }
  }

  return result;
}

std::string sum(const std::vector<std::string> &terms)
{
  std::string result;
  for(auto &term : terms)
  {
    if(result.empty())
      result = term;
    else if(term != "" && term[0] == '-')
      result += term;
    else
      result += "+" + term;
  }
  return result;
}

std::string ranking_net_to_string(
  const state_variablest &state_variables,
  const std::shared_ptr<RankingNet> net)
{
  std::vector<std::string> terms;

  auto weight = net->named_parameters()["fc1.weight"];
  auto bias = net->named_parameters()["fc1.bias"];

  for(auto &var : state_variables)
  {
    assert(var.second < state_variables.size());
    long long weight_int = round(weight[0][var.second].item<double>());
    if(weight_int == 0)
    {
    }
    else if(weight_int == 1)
    {
      terms.push_back(var.first);
    }
    else if(weight_int == -1)
    {
      terms.push_back("-" + var.first);
    }
    else
    {
      terms.push_back(std::to_string(weight_int) + "*" + var.first);
    }
  }

  long long bias_int = round(bias.item<double>());
  terms.push_back(std::to_string(bias_int));

  return sum(terms);
}

int main(int argc, const char *argv[])
{
  // The first argument is the directory with the VCD files.
  if(argc != 2)
  {
    std::cout << "Usage: nuterm trace_directory\n";
    return 1;
  }

  const auto traces = read_traces(argv[1]);

  auto state_variables = ::state_variables(traces);

  if(state_variables.empty())
  {
    std::cout << "no state variables\n";
    return 1;
  }

  for(auto &v : state_variables)
    std::cout << "V" << v.second << "=" << v.first << '\n';

  torch::manual_seed(0);

  const auto tensors = traces_to_tensors(state_variables, traces);

  std::cout << "Got " << tensors.size() << " transitions\n";

  const auto net = std::make_shared<RankingNet>(state_variables.size());

#if 0
  for(auto &p : net->named_parameters())
  {
    std::cout << p.key() << ": " << p.value() << "\n";
  }
#endif

  {
    auto weight = net->named_parameters()["fc1.weight"];
    auto bias = net->named_parameters()["fc1.bias"];
    assert(weight.dim() == 2);
    assert(bias.dim() == 1);
    std::cout << "#weights: " << weight.size(1) << "\n";
    assert(weight.size(1) == state_variables.size());

#if 0
    for(auto &var : state_variables)
    {
      assert(var.second < state_variables.size());
      std::cout << "weight " << var.first << " = " << weight[0][var.second].item<double>() << '\n';
    }

    std::cout << "bias: " << bias.item<double>() << "\n";
#endif
  }

  std::cout << "TRAINING\n";
  ranking_function_training(net, tensors);

  {
    auto weight = net->named_parameters()["fc1.weight"];
    auto bias = net->named_parameters()["fc1.bias"];
    for(auto &var : state_variables)
    {
      assert(var.second < state_variables.size());
      std::cout << "weight " << var.first << " = "
                << (long long)round(weight[0][var.second].item<double>()) << ' '
                << weight[0][var.second].item<double>() << '\n';
    }

    std::cout << "bias: " << (long long)(round(bias.item<double>())) << ' '
              << bias.item<double>() << "\n";
  }

  std::cout << "RESULT: " << ranking_net_to_string(state_variables, net)
            << '\n';
}
