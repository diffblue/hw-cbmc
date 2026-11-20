/*******************************************************************\

Module: FastPPA Frontend (Verilog parsing + transition system)

Author: Kiro

\*******************************************************************/

#include "fastppa_frontend.h"

#include <util/cmdline.h>
#include <util/namespace.h>

#include <ebmc/ebmc_error.h>
#include <verilog/verilog_ebmc_language.h>
#include <verilog/verilog_types.h>

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

  model.state_vars = model.transition_system.state_variables();

  const namespacet ns{model.transition_system.symbol_table};
  for(auto &port :
      to_module_type(model.transition_system.main_symbol->type).ports())
  {
    if(!port.output())
      continue;
    const symbolt *symbol;
    if(ns.lookup(port.identifier(), symbol))
      throw ebmc_errort{} << "output port " << port.identifier()
                          << " has no symbol";
    model.outputs.push_back(symbol->symbol_expr());
  }

  return model;
}
