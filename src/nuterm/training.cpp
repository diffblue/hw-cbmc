/*******************************************************************\

Module: Ranking Function Training

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "training.h"

#include <cassert>

const double delta = 1;

#include <iostream>

void ranking_function_training(
  std::shared_ptr<RankingNet> net,
  const std::vector<torch::Tensor> &data)
{
  assert(net != nullptr);

  for(auto &sample : data)
    assert(sample.size(0) == 2);

  // Form batches. These are 2 x batch-size x state-vars.
  std::vector<std::pair<torch::Tensor, torch::Tensor>> batches;
  std::size_t batch_size = 100;
  std::vector<torch::Tensor> batch_current, batch_next;
  batch_current.reserve(batch_size);
  batch_next.reserve(batch_size);

  for(auto &sample : data)
  {
    if(batch_current.size() == batch_size)
    {
      auto tensor_current = torch::stack(batch_current, 0);
      auto tensor_next = torch::stack(batch_next, 0);
      auto pair = std::pair<torch::Tensor, torch::Tensor>{std::move(tensor_current), std::move(tensor_next)};
      batches.push_back(std::move(pair));
      batch_current.clear();
      batch_next.clear();
    }
    else
    {
      batch_current.push_back(sample[0]);
      batch_next.push_back(sample[1]);
    }
  }

  std::cout << "BATCHES.size(): " << batches.size() << "\n";
  std::cout << "BATCHES[0].first.size(0): " << batches[0].first.size(0) << "\n";
  std::cout << "BATCHES[0].second.size(0): " << batches[0].second.size(0) << "\n";
  std::cout << "BATCHES[1].first.size(0): " << batches[1].first.size(0) << "\n";

  auto ranking_function_loss =
    [](const torch::Tensor &curr, const torch::Tensor &next) -> torch::Tensor {
    // these are batches
    assert(curr.dim() == 2 && next.dim() == 2);
    // The ranking needs to decrease from 'curr' to 'next'
    // by at least 'delta'. Anything less than that is loss.
    return torch::relu(next - curr + delta);
  };

#if 0
  torch::optim::SGD optimizer(net->parameters(), /*lr=*/0.1);
#endif
#if 1
  torch::optim::Adam optimizer(net->parameters(), /*lr=*/0.1);
#endif

  torch::Tensor last_loss = {};

  for(size_t epoch = 1; epoch <= 20; ++epoch)
  {
    size_t batch_index = 0;

    // Iterate the data loader to yield batches from the dataset.
    for(auto &batch : batches)
    {
      // std::cout << "B: " << batch << "\n";

      // Reset gradients.
      optimizer.zero_grad();

      // Execute the model on the input data vectors.
      torch::Tensor prediction_curr = net->forward(batch.first);
      torch::Tensor prediction_next = net->forward(batch.second);
      // std::cout << "B: " << std::fixed << batch[0][1].item<double>() << " -> " << batch[1][1].item<double>() << "\n";
      // std::cout << "R: " << std::fixed << prediction_curr.item<double>() << " -> " << prediction_next.item<double>() << "\n";
      std::cout << "prediction_curr: " << prediction_curr.dim() << "\n";
      return;

      // Compute a loss value to judge the prediction of our model.
      torch::Tensor loss =
        ranking_function_loss(prediction_curr, prediction_next);

      // std::cout << "L: " << loss << "\n";

      // Compute gradients of the loss w.r.t. the parameters of our model.
      loss.backward();

      // Update the parameters based on the calculated gradients.
      optimizer.step();

#if 1
      if(1)
      {
        std::cout << "Epoch: " << epoch << " | Batch: " << batch_index
                  << " | Loss: " << std::fixed << std::setprecision(3)
                  << loss.item<double>() << '\n';
        //torch::save(net, "net.pt");
      }
#endif

      batch_index++;

      last_loss = loss;
    }

    if(last_loss.item<double>() == 0)
      break; // done
  }

  std::cout << "Final loss: " << std::fixed << std::setprecision(3)
            << last_loss.item<double>() << '\n';
}
