/*******************************************************************\

Module: VHDL Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "vhdl_synthesis.h"
#include "vhdl_synthesis_class.h"

#include <util/mathematical_expr.h>
#include <util/std_expr.h>

#include <temporal-logic/ctl.h>

/*******************************************************************\

Function: vhdl_synthesist::synth_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_synthesist::synth_code(const codet &code)
{
  const irep_idt &statement = code.get_statement();

  if(statement == ID_assign)
  {
  }
  else if(statement == ID_vhdl_signal_assign)
  {
  }
  else if(statement == ID_skip)
  {
  }
  else if(statement == ID_ifthenelse)
  {
    // the branches may contain assertions
    auto &if_code = to_code_ifthenelse(code);
    synth_code(if_code.then_case());
    if(if_code.has_else_case())
      synth_code(if_code.else_case());
  }
  else if(statement == ID_block)
  {
    for(auto &op : code.operands())
      synth_code(to_code(op));
  }
  else if(statement == ID_assert)
  {
    DATA_INVARIANT(code.operands().size() == 1, "assert has one operand");

    // There is an implicit 'always'
    exprt property = AG_exprt(code.op0());

    // we'll add a property symbol
    symbolt new_symbol;

    new_symbol.base_name = "property" + std::to_string(++property_counter);
    new_symbol.name = id2string(module) + "." + id2string(new_symbol.base_name);
    new_symbol.is_property = true;
    new_symbol.mode = "VHDL";
    new_symbol.type = bool_typet();
    new_symbol.value = property;
    new_symbol.location = code.source_location();
    new_symbol.module = module_symbol->name;
    new_symbol.pretty_name = id2string(module_symbol->pretty_name) + "." +
                             id2string(new_symbol.base_name);

    auto &report = static_cast<const exprt &>(code.find(ID_vhdl_report));

    if(report.id() == ID_constant && report.type().id() == ID_string)
    {
      const constant_exprt &constant_expr = to_constant_expr(report);
      new_symbol.location.set_comment(
        "assertion " + id2string(constant_expr.get_value()));
    }

    if(symbol_table.add(new_symbol))
    {
      error() << "failed to add property symbol" << eom;
      throw 0;
    }
  }
  else
  {
    error() << "unexpected statement during synthesis: " << statement << eom;
    throw 0;
  }
}

/*******************************************************************\

Function: vhdl_synthesist::synth_module

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_synthesist::synth_module(const irept &module)
{
  PRECONDITION(module.id() == ID_module);

  const exprt &body = static_cast<const exprt &>(module.find(ID_body));

  for(auto &op : body.operands())
  {
    if(op.id() == ID_process)
      synth_process(op);
    else if(op.id() == ID_code)
      synth_code(to_code(op));
    else
    {
      error() << "unexpected module item during synthesis: " << op.id() << eom;
      throw 0;
    }
  }
}

/*******************************************************************\

Function: vhdl_synthesist::synth_process

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_synthesist::synth_process(const exprt &process)
{
  // the body of the process is operand 0
  synth_code(to_code(to_unary_expr(process).op()));
}

/*******************************************************************\

Function: vhdl_synthesist::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool vhdl_synthesist::operator()()
{
  try
  {
    auto s_it=symbol_table.get_writeable(module);

    if(s_it==nullptr)
    {
      error() << "module `" << module << "' not found" << eom;
      throw 0;
    }

    symbolt &symbol = *s_it;
    module_symbol = &symbol;

    property_counter = 0;

    synth_module(symbol.value);

    transt trans_expr{
      ID_trans,
      conjunction(invar),
      conjunction(init),
      conjunction(trans),
      symbol.type};

    symbol.value = trans_expr;

    return false;
  }
  catch(...)
  {
    return true;
  }
}

/*******************************************************************\

Function: vhdl_synthesis

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool vhdl_synthesis(
  symbol_table_baset &symbol_table,
  const irep_idt &module,
  message_handlert &message_handler)
{
  return vhdl_synthesist(symbol_table, module, message_handler)();
}
