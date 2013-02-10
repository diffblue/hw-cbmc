/*******************************************************************\

Module: Verilog Type Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <arith_tools.h>
#include <simplify_expr.h>
#include <replace_symbol.h>

#include "verilog_typecheck.h"

/*******************************************************************\

Function: verilog_typecheckt::get_parameter_values

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::get_parameter_values(
  const irept &module_source,
  const exprt::operandst &parameters,
  expr_listt &parameter_values)
{
  exprt::operandst::const_iterator p_it=parameters.begin();
  
  const irept &module_items=module_source.find(ID_module_items);
  
  replace_symbolt replace_symbol;

  forall_irep(it, module_items.get_sub())
    if(it->id()==ID_parameter_decl)
    {
      forall_operands(o_it, static_cast<const exprt &>(*it))
      {
        const irep_idt &identifier=o_it->get(ID_identifier);
        exprt value;
        
        if(p_it!=parameters.end())
        {
          value=*p_it;
          p_it++;
        }
        else
        {
          value=static_cast<const exprt &>(o_it->find(ID_value));
          // substitute other parameters
          replace_symbol.replace(value);
          simplify(value, ns);
          
          if(!value.is_constant())
          {
            err_location((const exprt &)(o_it->find(ID_value)));
            str << "parameter value expected to simplify to constant, "
                << "but got `" << to_string(value) << "'" << std::endl;
            throw 0;
          }
        }
        
        replace_symbol.insert(identifier, value);
        parameter_values.push_back(value);
      }
    }
    
  if(p_it!=parameters.end())
  {
    err_location(*p_it);
    throw "too many parameters";
  }
}

/*******************************************************************\

Function: verilog_typecheckt::set_parameter_values

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::set_parameter_values(
  irept &module_source,
  const expr_listt &parameter_values)
{
  expr_listt::const_iterator p_it=parameter_values.begin();
  
  irept &module_items=module_source.add(ID_module_items);
  
  forall_irep(it, module_items.get_sub())
    if(it->id()==ID_parameter_decl)
    {
      Forall_operands(o_it, (exprt &)*it)
      {
        assert(p_it!=parameter_values.end());
        
        exprt &value=static_cast<exprt &>(o_it->add(ID_value));
        value=*p_it;
        p_it++;
      }
    }
}

/*******************************************************************\

Function: verilog_typecheckt::module_instance

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::module_instance(
  const locationt &location,
  std::string &module_identifier,
  const exprt::operandst &parameters)
{
  if(parameters.empty()) return;

  // find base symbol
  
  symbol_tablet::symbolst::const_iterator it=
    symbol_table.symbols.find(module_identifier);
  
  if(it==symbol_table.symbols.end())
  {
    err_location(location);
    str << "module not found" << std::endl;
    throw 0;
  }
  
  const symbolt &base_symbol=it->second;
  
  expr_listt parameter_values;
  
  get_parameter_values(
    base_symbol.type.find(ID_module_source),
    parameters,
    parameter_values);

  // create full instance symbol name
  std::string suffix="(";
  
  bool first=true;
  forall_expr_list(it, parameter_values)
    if(it->is_not_nil())
    {
      if(first) first=false; else suffix+=",";
      
      mp_integer i;
      if(to_integer(*it, i))
      {
        err_location(*it);
        str << "parameter expected to be constant, but got `"
            << to_string(*it) << "'" << std::endl;
        throw 0;
      }
      else
        suffix+=integer2string(i);
    }
    
  suffix+=')';

  module_identifier+=suffix;
  
  if(symbol_table.symbols.find(module_identifier)!=
     symbol_table.symbols.end())
    return; // done already
    
  // create symbol
  
  symbolt symbol(base_symbol);

  symbol.name=module_identifier;
  symbol.module=symbol.name;
  
  // set parameters
  set_parameter_values(
    symbol.type.add(ID_module_source),
    parameter_values);
  
  // throw away old stuff
  symbol.value.clear();

  // put symbol in symbol_table

  symbolt *new_symbol;

  if(symbol_table.move(symbol, new_symbol))
  {
    err_location(location);
    str << "duplicate definition of module " 
        << symbol.base_name << std::endl;
    throw 0;
  }

  // recursive call

  verilog_typecheckt verilog_typecheck(*new_symbol, symbol_table, get_message_handler());

  if(verilog_typecheck.typecheck_main())
    throw 0;
}

