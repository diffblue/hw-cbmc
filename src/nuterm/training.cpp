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
  const std::vector<batcht> &batches)
{
  assert(net != nullptr);

  std::cout << "BATCHES[0].curr.size(0): " << batches[0].curr.size(0) << "\n";
  std::cout << "BATCHES[0].curr.size(1): " << batches[0].curr.size(1) << "\n";

  auto ranking_function_loss =
    [](const torch::Tensor &curr, const torch::Tensor &next) -> torch::Tensor {
    // these are batches
    assert(curr.dim() == 2 && next.dim() == 2);
    // The ranking needs to decrease from 'curr' to 'next'
    // by at least 'delta'. Anything less than that is loss.
    auto point_loss = torch::relu(next - curr + delta);
    auto loss = torch::sum(point_loss);
    assert(loss.dim() == 0);
    return loss;
  };

#if 0
  torch::optim::SGD optimizer(net->parameters(), /*lr=*/0.1);
#endif
#if 1
  torch::optim::Adam optimizer(net->parameters(), /*lr=*/0.001);
#endif

  double epoch_loss;

  for(size_t epoch = 1; epoch <= 20; ++epoch)
  {
    size_t batch_index = 0;
    epoch_loss = 0;

    // Iterate the data loader to yield batches from the dataset.
    for(auto &batch : batches)
    {
      // std::cout << "batch.curr: " << batch.curr << "\n";

      // Reset gradients.
      optimizer.zero_grad();

      // Execute the model on the input data vectors.
      torch::Tensor prediction_curr = net->forward(batch.curr);
      torch::Tensor prediction_next = net->forward(batch.next);
      // std::cout << "B: " << std::fixed << batch[0][1].item<double>() << " -> " << batch[1][1].item<double>() << "\n";
      // std::cout << "R: " << std::fixed << prediction_curr.item<double>() << " -> " << prediction_next.item<double>() << "\n";
      //std::cout << "prediction_curr: " << prediction_curr.dim() << "\n";
      //return;

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
                  << " | Batch Loss: " << std::fixed << std::setprecision(3)
                  << loss.item<double>() << '\n';
        //torch::save(net, "net.pt");
      }
#endif

      batch_index++;

      epoch_loss += loss.item<double>();
    }

    if(epoch_loss == 0)
      break; // done
  }

  std::cout << "Final loss: " << std::fixed << std::setprecision(3)
            << epoch_loss << '\n';
}
