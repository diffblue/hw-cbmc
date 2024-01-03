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
  auto ranking_function_loss =
    [](const torch::Tensor &curr, const torch::Tensor &next) -> torch::Tensor
  {
    assert(curr.dim() == 1 && next.dim() == 1);
    // The ranking needs to decrease from 'curr' to 'next'
    // by at least 'delta'. Anything less than that is loss.
    return torch::relu(next - curr + delta);
  };

  torch::optim::SGD optimizer(net->parameters(), /*lr=*/0.1);
  torch::Tensor last_loss = {};

  for(size_t epoch = 1; epoch <= 10; ++epoch)
  {
    size_t batch_index = 0;

    // Iterate the data loader to yield batches from the dataset.
    for(auto &batch : data)
    {
      // Reset gradients.
      optimizer.zero_grad();

      // Execute the model on the input data.
      assert(batch.size(1) == 2);
      torch::Tensor prediction_curr = net->forward(batch[0]);
      torch::Tensor prediction_next = net->forward(batch[1]);
      //      std::cout << "B: " << std::fixed << batch[0][1].item<double>() << " -> " << batch[1][1].item<double>() << "\n";
      //      std::cout << "R: " << std::fixed << prediction_curr.item<double>() << " -> " << prediction_next.item<double>() << "\n";

      // Compute a loss value to judge the prediction of our model.
      torch::Tensor loss =
        ranking_function_loss(prediction_curr, prediction_next);

      // Compute gradients of the loss w.r.t. the parameters of our model.
      loss.backward();

      // Update the parameters based on the calculated gradients.
      optimizer.step();

#if 0
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
  }

  std::cout << "Final loss: " << std::fixed << std::setprecision(3)
            << last_loss.item<double>() << '\n';
}
