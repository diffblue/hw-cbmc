/*******************************************************************\

Module: Training

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <torch/torch.h>

#include <iostream>

struct RankingNet : torch::nn::Module
{
  explicit RankingNet(std::size_t number_of_state_variables)
  {
    fc1 =
      register_module("fc1", torch::nn::Linear(number_of_state_variables, 1));
    fc1->to(torch::kFloat64);
#if 0
    // The default values for nn::Linear are kaiming_uniform(sqrt(5)).
    // Use zeros instead.
    fc1->named_parameters()["weight"].fill_(0, torch::requires_grad());
    fc1->named_parameters()["bias"] = torch::zeros({1}); // .fill_(0, torch::requires_grad());
    std::cout << "CON: " << fc1->named_parameters()["bias"].item<double>() << "\n";
#endif
  }

  torch::Tensor forward(torch::Tensor x)
  {
    // the relu ensures that the function is bounded from below by 0
    // return torch::relu(fc1->forward(x));
    return fc1->forward(x);
  }

  torch::nn::Linear fc1{nullptr};
};

void ranking_function_training(
  const std::shared_ptr<RankingNet> net,
  const std::vector<torch::Tensor> &);
