/*******************************************************************\

Module: Neural Liveness

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef EBMC_NEURAL_LIVENESS_H
#define EBMC_NEURAL_LIVENESS_H

class cmdlinet;
class message_handlert;
class transition_systemt;

int do_neural_liveness(
  transition_systemt &,
  const cmdlinet &,
  message_handlert &);

#endif // EBMC_NEURAL_LIVENESS_H
