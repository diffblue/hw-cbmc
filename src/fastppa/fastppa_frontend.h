/*******************************************************************\

Module: FastPPA Frontend (Verilog parsing + transition system)

Author: Kiro

\*******************************************************************/

#ifndef CPROVER_FASTPPA_FASTPPA_FRONTEND_H
#define CPROVER_FASTPPA_FASTPPA_FRONTEND_H

#include <util/std_expr.h>

#include <ebmc/transition_system.h>
#include <trans-word-level/word_level_trans.h>

#include <memory>
#include <vector>

class cmdlinet;
class message_handlert;

struct fastppa_modelt
{
  transition_systemt transition_system;
  std::unique_ptr<word_level_transt> wl_trans;
  std::vector<symbol_exprt> state_vars;
};

fastppa_modelt build_fastppa_model(const cmdlinet &, message_handlert &);

#endif // CPROVER_FASTPPA_FASTPPA_FRONTEND_H
