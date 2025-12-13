/*******************************************************************\

Module: Transition Systems for EBMC

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "transition_system.h"

#include <util/cmdline.h>
#include <util/config.h>
#include <util/get_module.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/options.h>
#include <util/unicode.h>

#include <langapi/language.h>
#include <langapi/language_util.h>
#include <langapi/mode.h>
#include <trans-word-level/show_module_hierarchy.h>
#include <verilog/verilog_types.h>

#include "ebmc_error.h"
#include "ebmc_language_file.h"
#include "ebmc_version.h"
#include "output_file.h"

#include <fstream>
#include <iostream>

static void output(
  const exprt &expr,
  std::ostream &out,
  languaget &language,
  const namespacet &ns)
{
  if(expr.id() == ID_and)
  {
    for(auto &conjunct : expr.operands())
      output(conjunct, out, language, ns);
  }
  else
  {
    std::string text;

    if(language.from_expr(expr, text, ns))
    {
      throw ebmc_errort() << "failed to convert expression";
    }

    out << "  " << text << '\n' << '\n';
  }
}

void transition_systemt::output(std::ostream &out) const
{
  auto language = get_language_from_mode(main_symbol->mode);

  const namespacet ns{symbol_table};

  out << "Initial state constraints:\n\n";

  ::output(trans_expr.init(), out, *language, ns);

  out << "State constraints:\n\n";

  ::output(trans_expr.invar(), out, *language, ns);

  out << "Transition constraints:\n\n";

  ::output(trans_expr.trans(), out, *language, ns);
}

std::vector<symbol_exprt> transition_systemt::state_variables() const
{
  std::vector<symbol_exprt> state_variables;

  const auto &module_symbol = *main_symbol;
  const namespacet ns(symbol_table);

  const auto &symbol_module_map = symbol_table.symbol_module_map;
  auto lower = symbol_module_map.lower_bound(module_symbol.name);
  auto upper = symbol_module_map.upper_bound(module_symbol.name);

  for(auto it = lower; it != upper; it++)
  {
    const symbolt &symbol = ns.lookup(it->second);

    if(symbol.is_state_var)
      state_variables.push_back(symbol.symbol_expr());
  }

  return state_variables;
}

std::vector<symbol_exprt> transition_systemt::inputs() const
{
  std::vector<symbol_exprt> inputs;

  const auto &module_symbol = *main_symbol;

  DATA_INVARIANT(
    module_symbol.type.id() == ID_module, "main_symbol must be module");

  // filter out the inputs
  auto &ports = to_module_type(module_symbol.type).ports();
  for(auto &port : ports)
  {
    DATA_INVARIANT(port.id() == ID_symbol, "port must be a symbol");
    if(port.input() && !port.output())
    {
      symbol_exprt input_symbol(port.identifier(), port.type());
      input_symbol.add_source_location() = port.source_location();
      inputs.push_back(std::move(input_symbol));
    }
  }

  return inputs;
}
