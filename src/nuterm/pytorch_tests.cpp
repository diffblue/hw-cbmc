#include <torch/torch.h>

#include <assert.h>
#include <cmath>

struct test_net : torch::nn::Module
{
  test_net()
  {
    fc1 = register_module("fc1", torch::nn::Linear(1, 1));
    fc1->to(torch::kFloat64);
  }

  torch::Tensor forward(torch::Tensor x)
  {
    return fc1->forward(x);
  }

  torch::nn::Linear fc1{nullptr};
};

struct test_batcht
{
  torch::Tensor data;
  torch::Tensor target;
};

void train(
  std::shared_ptr<test_net> net,
  const std::vector<test_batcht> &batches)
{
  torch::optim::SGD optimizer(net->parameters(), /*lr=*/0.1);

  for(size_t epoch = 1; epoch <= 30; ++epoch)
  {
    size_t batch_index = 0;

    // Iterate the data loader to yield batches from the dataset.
    for(auto &batch : batches)
    {
      // Reset gradients.
      optimizer.zero_grad();

      // Execute the model on the input data.
      torch::Tensor prediction = net->forward(batch.data);

      // Compute a loss value to judge the prediction of our model.
      torch::Tensor loss = torch::mse_loss(prediction, batch.target);

      // Compute gradients of the loss w.r.t. the parameters of our model.
      loss.backward();

      // Update the parameters based on the calculated gradients.
      optimizer.step();
    }
  }
}

void pytorch_test1()
{
  torch::manual_seed(0);

  auto net = std::make_shared<test_net>();

  std::vector<test_batcht> batches = {
    {.data = torch::full({1}, /*value*/ 0, torch::kFloat64),
     .target = torch::full({1}, /*value*/ 10, torch::kFloat64)},
    {.data = torch::full({1}, /*value*/ 1, torch::kFloat64),
     .target = torch::full({1}, /*value*/ 11, torch::kFloat64)},
    {.data = torch::full({1}, /*value*/ 2, torch::kFloat64),
     .target = torch::full({1}, /*value*/ 12, torch::kFloat64)}};

  train(net, batches);

  assert(round(net->parameters()[0].item<double>()) == 1);  // coefficient
  assert(round(net->parameters()[1].item<double>()) == 10); // bias
}

void pytorch_test2()
{
  torch::manual_seed(0);

  auto net = std::make_shared<test_net>();

  std::vector<test_batcht> batches = {
    {.data = torch::full({1}, /*value*/ 0, torch::kFloat64),
     .target = torch::full({1}, /*value*/ 0, torch::kFloat64)},
    {.data = torch::full({1}, /*value*/ 1, torch::kFloat64),
     .target = torch::full({1}, /*value*/ -1, torch::kFloat64)},
    {.data = torch::full({1}, /*value*/ 2, torch::kFloat64),
     .target = torch::full({1}, /*value*/ -2, torch::kFloat64)}};

  train(net, batches);

  assert(round(net->parameters()[0].item<double>()) == -1); // coefficient
  assert(round(net->parameters()[1].item<double>()) == 0);  // bias
}

void pytorch_test3()
{
  torch::manual_seed(0);

  auto net = std::make_shared<test_net>();

  std::vector<test_batcht> batches = {
    {.data = torch::full({1}, /*value*/ 0, torch::kFloat64),
     .target = torch::full({1}, /*value*/ 10, torch::kFloat64)},
    {.data = torch::full({1}, /*value*/ 1, torch::kFloat64),
     .target = torch::full({1}, /*value*/ 9, torch::kFloat64)},
    {.data = torch::full({1}, /*value*/ 2, torch::kFloat64),
     .target = torch::full({1}, /*value*/ 8, torch::kFloat64)}};

  train(net, batches);

  assert(round(net->parameters()[0].item<double>()) == -1); // coefficient
  assert(round(net->parameters()[1].item<double>()) == 10); // bias
}

void pytorch_test4()
{
  torch::manual_seed(0);

  auto net = std::make_shared<test_net>();

  std::vector<torch::Tensor> data = {
    torch::full({1}, /*value*/ 0, torch::kFloat64),
    torch::full({1}, /*value*/ 1, torch::kFloat64),
    torch::full({1}, /*value*/ 2, torch::kFloat64),
    torch::full({1}, /*value*/ 3, torch::kFloat64),
    torch::full({1}, /*value*/ 4, torch::kFloat64),
    torch::full({1}, /*value*/ 5, torch::kFloat64)};

  auto my_loss = [](const torch::Tensor &input) -> torch::Tensor {
    return input.abs();
  };

  torch::optim::SGD optimizer(net->parameters(), /*lr=*/0.1);

  for(size_t epoch = 1; epoch <= 10; ++epoch)
  {
    size_t batch_index = 0;

    // Iterate the data loader to yield batches from the dataset.
    for(auto &batch : data)
    {
      // Reset gradients.
      optimizer.zero_grad();

      // Execute the model on the input data.
      torch::Tensor prediction = net->forward(batch);

      // Compute a loss value to judge the prediction of our model.
      torch::Tensor loss = my_loss(prediction);

      // Compute gradients of the loss w.r.t. the parameters of our model.
      loss.backward();

      // Update the parameters based on the calculated gradients.
      optimizer.step();
    }
  }

  assert(round(net->parameters()[0].item<double>()) == 0); // coefficient
  assert(round(net->parameters()[1].item<double>()) == 0); // bias
}

struct test_net2 : torch::nn::Module
{
  explicit test_net2(std::size_t number_of_inputs)
  {
    fc1 = register_module("fc1", torch::nn::Linear(number_of_inputs, 1));
    fc1->to(torch::kFloat64);
  }

  torch::Tensor forward(torch::Tensor x)
  {
    x = fc1->forward(x);
    // the relu ensures x is bounded from below
    x = torch::relu(x);
    return x;
  }

  torch::nn::Linear fc1{nullptr};
};

void pytorch_test5()
{
  torch::manual_seed(0);

  auto net = std::make_shared<test_net2>(2);

  std::vector<torch::Tensor> data = {
    torch::tensor({0, 0}, torch::kFloat64),
    torch::tensor({1, 0}, torch::kFloat64),
    torch::tensor({2, 0}, torch::kFloat64),
    torch::tensor({3, 0}, torch::kFloat64),
    torch::tensor({4, 0}, torch::kFloat64),
    torch::tensor({5, 0}, torch::kFloat64)};

  auto my_loss = [](const torch::Tensor &input) -> torch::Tensor {
    return input.abs();
  };

  torch::optim::SGD optimizer(net->parameters(), /*lr=*/0.1);

  for(size_t epoch = 1; epoch <= 10; ++epoch)
  {
    size_t batch_index = 0;

    // Iterate the data loader to yield batches from the dataset.
    for(auto &batch : data)
    {
      // Reset gradients.
      optimizer.zero_grad();

      // Execute the model on the input data.
      torch::Tensor prediction = net->forward(batch);

      // Compute a loss value to judge the prediction of our model.
      torch::Tensor loss = my_loss(prediction);

      // Compute gradients of the loss w.r.t. the parameters of our model.
      loss.backward();

      // Update the parameters based on the calculated gradients.
      optimizer.step();
    }
  }

  assert(round(net->parameters()[0][0][0].item<double>()) == 0); // coefficient
  assert(round(net->parameters()[0][0][1].item<double>()) == 0); // coefficient
  assert(round(net->parameters()[1].item<double>()) == -1);      // bias
}

void pytorch_test6()
{
  torch::manual_seed(0);

  auto net = std::make_shared<test_net2>(1);

  // one state variable, pairs are transitions
  std::vector<torch::Tensor> data = {
    torch::stack(
      {torch::tensor({5}, torch::kFloat64),
       torch::tensor({4}, torch::kFloat64)}),
    torch::stack(
      {torch::tensor({4}, torch::kFloat64),
       torch::tensor({3}, torch::kFloat64)}),
    torch::stack(
      {torch::tensor({3}, torch::kFloat64),
       torch::tensor({2}, torch::kFloat64)}),
    torch::stack(
      {torch::tensor({2}, torch::kFloat64),
       torch::tensor({1}, torch::kFloat64)}),
    torch::stack(
      {torch::tensor({1}, torch::kFloat64),
       torch::tensor({0}, torch::kFloat64)})};

  auto my_loss =
    [](const torch::Tensor &curr, const torch::Tensor &next) -> torch::Tensor {
    return torch::relu(next - curr + 1.0);
  };

  torch::optim::SGD optimizer(net->parameters(), /*lr=*/0.1);

  for(size_t epoch = 1; epoch <= 3; ++epoch)
  {
    size_t batch_index = 0;

    // Iterate the data loader to yield batches from the dataset.
    for(auto &batch : data)
    {
      // Reset gradients.
      optimizer.zero_grad();

      // Execute the model on the input data.
      torch::Tensor prediction_curr = net->forward(batch[0]);
      torch::Tensor prediction_next = net->forward(batch[1]);

      // Compute a loss value to judge the prediction of our model.
      torch::Tensor loss = my_loss(prediction_curr, prediction_next);

      // Compute gradients of the loss w.r.t. the parameters of our model.
      loss.backward();

      // Update the parameters based on the calculated gradients.
      optimizer.step();
    }
  }

  assert(round(net->parameters()[0].item<double>()) == 1); // coefficient
  assert(round(net->parameters()[1].item<double>()) == 1); // bias
}

void pytorch_test7()
{
  torch::manual_seed(0);

  auto net = std::make_shared<test_net2>(2);

  // two state variables, pairs are transitions
  std::vector<torch::Tensor> data = {
    torch::stack(
      {torch::tensor({0, 5}, torch::kFloat64),
       torch::tensor({0, 4}, torch::kFloat64)}),
    torch::stack(
      {torch::tensor({0, 4}, torch::kFloat64),
       torch::tensor({0, 3}, torch::kFloat64)}),
    torch::stack(
      {torch::tensor({0, 3}, torch::kFloat64),
       torch::tensor({0, 2}, torch::kFloat64)}),
    torch::stack(
      {torch::tensor({0, 2}, torch::kFloat64),
       torch::tensor({0, 1}, torch::kFloat64)}),
    torch::stack(
      {torch::tensor({0, 1}, torch::kFloat64),
       torch::tensor({0, 0}, torch::kFloat64)})};

  auto my_loss =
    [](const torch::Tensor &curr, const torch::Tensor &next) -> torch::Tensor {
    return torch::relu(next - curr + 1.0);
  };

  torch::optim::SGD optimizer(net->parameters(), /*lr=*/0.1);

  for(size_t epoch = 1; epoch <= 3; ++epoch)
  {
    size_t batch_index = 0;

    // Iterate the data loader to yield batches from the dataset.
    for(auto &batch : data)
    {
      // Reset gradients.
      optimizer.zero_grad();

      // Execute the model on the input data.
      torch::Tensor prediction_curr = net->forward(batch[0]);
      torch::Tensor prediction_next = net->forward(batch[1]);

      // Compute a loss value to judge the prediction of our model.
      torch::Tensor loss = my_loss(prediction_curr, prediction_next);

      // Compute gradients of the loss w.r.t. the parameters of our model.
      loss.backward();
      //std::cout << "L " << loss.item<double>() << "\n";

      // Update the parameters based on the calculated gradients.
      optimizer.step();
    }
  }

  //std::cout << "XX: " << net->parameters() << "\n";
  //std::cout << "C: " << net->parameters()[0][0][0].item<double>() << "\n";
  //std::cout << "C: " << net->parameters()[0][0][1].item<double>() << "\n";
  //std::cout << "B: " << net->parameters()[1].item<double>() << "\n";
  assert(round(net->parameters()[0][0][0].item<double>()) == 0); // coefficient
  assert(round(net->parameters()[0][0][1].item<double>()) == 1); // coefficient
  assert(round(net->parameters()[1].item<double>()) == 0);       // bias
}

void pytorch_test8()
{
  torch::manual_seed(0);

  auto net = std::make_shared<test_net2>(1);

  // one state variable, pairs are transitions
  std::vector<torch::Tensor> data = {
    torch::stack(
      {torch::tensor({1}, torch::kFloat64),
       torch::tensor({2}, torch::kFloat64)}),
    torch::stack(
      {torch::tensor({2}, torch::kFloat64),
       torch::tensor({3}, torch::kFloat64)}),
    torch::stack(
      {torch::tensor({3}, torch::kFloat64),
       torch::tensor({4}, torch::kFloat64)}),
    torch::stack(
      {torch::tensor({4}, torch::kFloat64),
       torch::tensor({5}, torch::kFloat64)}),
    torch::stack(
      {torch::tensor({5}, torch::kFloat64),
       torch::tensor({6}, torch::kFloat64)})};

  auto my_loss =
    [](const torch::Tensor &curr, const torch::Tensor &next) -> torch::Tensor {
    // std::cout << "LL " << from.item<double>() << " -> " << to.item<double>() << "\n";
    return torch::relu(next - curr + 1.0);
  };

  //torch::optim::SGD optimizer(net->parameters(), /*lr=*/0.1);
  torch::optim::Adam optimizer(net->parameters(), /*lr=*/0.1);

  for(size_t epoch = 1; epoch <= 30; ++epoch)
  {
    size_t batch_index = 0;

    // Iterate the data loader to yield batches from the dataset.
    for(auto &batch : data)
    {
      // Reset gradients.
      optimizer.zero_grad();

      // Execute the model on the input data.
      torch::Tensor prediction_curr = net->forward(batch[0]);
      torch::Tensor prediction_next = net->forward(batch[1]);

      // Compute a loss value to judge the prediction of our model.
      torch::Tensor loss = my_loss(prediction_curr, prediction_next);

      // Compute gradients of the loss w.r.t. the parameters of our model.
      loss.backward();

      // Update the parameters based on the calculated gradients.
      optimizer.step();

      // std::cout << "L " << loss.item<double>() << "\n";
    }
  }

  //std::cout << "C: " << net->parameters()[0].item<double>() << "\n";
  //std::cout << "B: " << net->parameters()[1].item<double>() << "\n";
  assert(round(net->parameters()[0].item<double>()) == -1); // coefficient
  assert(round(net->parameters()[1].item<double>()) == 6);  // bias
}

int main()
{
  std::cout << "Running tests\n";

  pytorch_test1();
  pytorch_test2();
  pytorch_test3();
  pytorch_test4();
  pytorch_test5();
  pytorch_test6();
  pytorch_test7();
  pytorch_test8();
}
