/*******************************************************************\

Module: nuterm main

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "training.h"
#include "traces_to_tensors.h"

#include <algorithm>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <list>
#include <string>

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
    //std::cout << "Reading " << entry << '\n';
    std::ifstream in(entry);
    traces.push_back(vcd_parser(in));
  }

  std::cout << "Read " << traces.size() << " trace files\n";

  return traces;
}

state_variablest state_variables(const tracest &traces)
{
  // number all identifiers
  state_variablest state_variables;

  for(auto &trace : traces)
  {
    for(auto &[id, var] : trace.var_map)
    {
      if(state_variables.find(id) == state_variables.end())
      {
        auto &state_variable = state_variables[id];
        state_variable.index = state_variables.size() - 1;
        state_variable.reference = var.reference;
      }
    }
  }

  return state_variables;
}

bool has_suffix(const std::string &s, const std::string &suffix)
{
  if(s.length() >= suffix.length())
    return s.compare(s.length() - suffix.length(), suffix.length(), suffix) ==
           0;
  else
    return false;
}

std::string liveness_signal(const state_variablest &state_variables)
{
  for(auto &[id, var] : state_variables)
    if(var.reference == "$live")
      return id;

  std::cout.flush();
  std::cerr << "failed to find liveness signal" << '\n';

  abort();
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

  for(auto &[id, var] : state_variables)
  {
    assert(var.index < state_variables.size());
    long long weight_int = round(weight[0][var.index].item<double>());
    if(weight_int == 0)
    {
    }
    else if(weight_int == 1)
    {
      terms.push_back(var.reference);
    }
    else
    {
      if(weight_int >= 0)
        terms.push_back(std::to_string(weight_int) + "*" + var.reference);
      else
      {
        // make signed, but first add a bit
        terms.push_back(
          std::to_string(weight_int) + "*$signed({1'b0," + var.reference +
          "})");
      }
    }
  }

  long long bias_int = round(bias.item<double>());
  if(bias_int != 0)
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

  auto liveness_signal = ::liveness_signal(state_variables);

  for(auto &[_, var] : state_variables)
    std::cout << "V" << var.index << "=" << var.reference << '\n';

  std::cout << "Liveness signal: " << liveness_signal << '\n';

  torch::manual_seed(0);

  const std::size_t batch_size = 1000;

  const auto batches =
    traces_to_tensors(state_variables, liveness_signal, traces, batch_size);

  std::cout << "Got " << batches.size() << " batch(es) to rank\n";

  if(batches.empty())
  {
    return 0;
  }

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
  ranking_function_training(net, batches);

  {
    auto weight = net->named_parameters()["fc1.weight"];
    auto bias = net->named_parameters()["fc1.bias"];
    for(auto &[_, var] : state_variables)
    {
      assert(var.index < state_variables.size());
      std::cout << "weight " << var.reference << " = "
                << (long long)round(weight[0][var.index].item<double>()) << ' '
                << weight[0][var.index].item<double>() << '\n';
    }

    std::cout << "bias: " << (long long)(round(bias.item<double>())) << ' '
              << bias.item<double>() << "\n";
  }

  std::cout << "RESULT: " << ranking_net_to_string(state_variables, net)
            << '\n';
}
