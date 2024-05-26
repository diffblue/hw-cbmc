/*******************************************************************\

Module: Batch

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef NUTERM_BATCH_H
#define NUTERM_BATCH_H

#include <torch/torch.h>

struct batcht
{
  batcht(const std::vector<torch::Tensor> &__curr, const std::vector<torch::Tensor> &__next) : curr(torch::stack(__curr)), next(torch::stack(__next)) { }
  torch::Tensor curr, next;
};

#endif // NUTERM_BATCH_H
