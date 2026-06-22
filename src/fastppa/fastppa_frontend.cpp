/*******************************************************************\

Module: FastPPA Frontend (Verilog parsing + transition system)

Author: Kiro

\*******************************************************************/

#include "fastppa_frontend.h"

#include <util/cmdline.h>

#include <ebmc/ebmc_error.h>
#include <verilog/verilog_ebmc_language.h>

fastppa_modelt
build_fastppa_model(const cmdlinet &cmdline, message_handlert &message_handler)
{
  fastppa_modelt model;

  // Parse Verilog and build transition system
  verilog_ebmc_languaget language(cmdline, message_handler);
  auto ts_opt = language.transition_system();

  if(!ts_opt.has_value())
    throw ebmc_errort{} << "failed to build transition system";

  model.transition_system = std::move(ts_opt.value());

  // Build word-level next-state functions
  const namespacet ns(model.transition_system.symbol_table);
  model.wl_trans = std::make_unique<word_level_transt>(ns);
  try
  {
    model.wl_trans->read_trans(model.transition_system.trans_expr);
  }
  catch(...)
  {
    // Combinational design — no next-state functions, that's OK
  }

  model.state_vars = model.transition_system.state_variables();

  return model;
}
