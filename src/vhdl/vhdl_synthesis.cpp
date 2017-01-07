/*******************************************************************\

Module: VHDL Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>

#include "vhdl_synthesis.h"
#include "vhdl_synthesis_class.h"

/*******************************************************************\

Function: vhdl_synthesist::synth_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void vhdl_synthesist::synth_code(const codet &code)
{
  const irep_idt &statement=code.get_statement();
  
  if(statement==ID_assign)
  {
  }
  else if(statement==ID_continuous_assign)
  {
  }
  else if(statement==ID_assert)
  {
    assert(code.operands().size()==3);
    
    // There is an implicit 'always'
    exprt property=unary_predicate_exprt(ID_AG, code.op0());
  
    // we'll add a property symbol
    symbolt new_symbol;
    
    new_symbol.base_name="property"+std::to_string(++property_counter);
    new_symbol.name=id2string(module)+"."+id2string(new_symbol.base_name);
    new_symbol.is_property=true;
    new_symbol.mode="VHDL";
    new_symbol.type=bool_typet();
    new_symbol.value=property;
    new_symbol.location=code.source_location();
    new_symbol.module=module_symbol->name;
    new_symbol.pretty_name=
      id2string(module_symbol->pretty_name)+"."+id2string(new_symbol.base_name);

    if(code.op1().id()==ID_constant &&
       code.op1().type().id()==ID_string)
    {
      const constant_exprt &constant_expr=to_constant_expr(code.op1());
      new_symbol.location.set_comment("assertion "+id2string(constant_expr.get_value()));
    }
    
    if(symbol_table.move(new_symbol))
    {
      error() << "failed to add property symbol" << eom;
      throw 0;
    }
  }
  else
  {
    error() << "unexpected statement during synthesis: "
            << statement << eom;
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
  assert(module.id()==ID_module);
  
  const exprt &body=static_cast<const exprt &>(module.find(ID_body));

  for(auto & op : body.operands())
  {
    if(op.id()==ID_process)
      synth_process(op);
    else
    {
      error() << "unexpected module item during synthesis: "
              << op.id() << eom;
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
  for(auto & op : process.operands())
    synth_code(to_code(op));
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
    symbol_tablet::symbolst::iterator s_it=
      symbol_table.symbols.find(module);

    if(s_it==symbol_table.symbols.end())
    {
      error() << "module `" << module << "' not found" << eom;
      throw 0;
    }
    
    symbolt &symbol=s_it->second;
    module_symbol=&symbol;

    property_counter=0;
    
    synth_module(symbol.value);
    
    transt trans_expr;

    trans_expr.invar()=conjunction(invar);
    trans_expr.init()=conjunction(init);
    trans_expr.trans()=conjunction(trans);
    
    symbol.value=trans_expr;
    
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
  symbol_tablet &symbol_table,
  const irep_idt &module,
  message_handlert &message_handler)
{
  return vhdl_synthesist(symbol_table, module, message_handler)();
}
