/*******************************************************************\

Module: Verilog Type Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/ebmc_util.h>
#include <util/replace_symbol.h>
#include <util/simplify_expr.h>

#include "verilog_typecheck.h"

#include "verilog_expr.h"

/*******************************************************************\

Function: verilog_typecheckt::get_parameter_declarators

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::vector<verilog_parameter_declt::declaratort>
verilog_typecheckt::get_parameter_declarators(const irept &module_source)
{
  std::vector<verilog_parameter_declt::declaratort> declarators;

  const irept &module_items = module_source.find(ID_module_items);

  for(auto &item : module_items.get_sub())
    if(item.id() == ID_parameter_decl)
      for(auto &decl : to_verilog_parameter_decl(item).declarations())
        declarators.push_back(decl);

  const irept &parameter_port_list = module_source.find("parameter_port_list");

  for(auto &decl : parameter_port_list.get_sub())
    declarators.push_back(
      static_cast<const verilog_parameter_declt::declaratort &>(decl));

  return declarators;
}

/*******************************************************************\

Function: verilog_typecheckt::get_parameter_values

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::list<exprt> verilog_typecheckt::get_parameter_values(
  const irept &module_source,
  const exprt::operandst &parameter_assignment,
  const std::map<irep_idt, exprt> &instance_defparams)
{
  const auto parameter_declarators = get_parameter_declarators(module_source);
  replace_symbolt replace_symbol;

  std::list<exprt> parameter_values;

  // Are the parameter values given with the instantiation
  // statement named or ordered?
  if(!parameter_assignment.empty() &&
     parameter_assignment.front().id()==ID_named_parameter_assignment)
  {
    std::map<irep_idt, exprt> map;

    forall_expr(it, parameter_assignment)
    {
      irep_idt parameter=it->get(ID_parameter);
      map[parameter]=static_cast<const exprt &>(it->find(ID_value));
    }

    for(auto &decl : parameter_declarators)
    {
      auto &identifier = decl.identifier();
      exprt value;

      if(map.find(identifier) != map.end())
        value = map[identifier];
      else
      {
        // The default value is not yet converted.
        value = decl.value();
        convert_expr(value);

        // substitute other parameters
        replace_symbol.replace(value);
        simplify(value, ns);

        if(!value.is_constant())
        {
          error().source_location = value.source_location();
          error() << "parameter value expected to simplify to constant, "
                  << "but got `" << to_string(value) << "'" << eom;
          throw 0;
        }
      }

      // Is there a defparam that overrides this parameter?
      auto def_param_it = instance_defparams.find(identifier);
      if(def_param_it != instance_defparams.end())
        value = def_param_it->second;

      replace_symbol.insert(symbol_exprt{identifier, value.type()}, value);
      parameter_values.push_back(value);
    }
  }
  else
  {
    // ordered
    exprt::operandst::const_iterator p_it=parameter_assignment.begin();

    for(auto &decl : parameter_declarators)
    {
      exprt value;

      if(p_it != parameter_assignment.end())
      {
        value = *p_it;
        p_it++;
      }
      else
      {
        // The default value is not yet converted.
        value = decl.value();
        convert_expr(value);

        // substitute other parameters
        replace_symbol.replace(value);
        simplify(value, ns);

        if(!value.is_constant())
        {
          error().source_location = value.source_location();
          error() << "parameter value expected to simplify to constant, "
                  << "but got `" << to_string(value) << "'" << eom;
          throw 0;
        }
      }

      // Is there a defparam that overrides this parameter?
      auto &identifier = decl.identifier();
      auto def_param_it = instance_defparams.find(identifier);
      if(def_param_it != instance_defparams.end())
        value = def_param_it->second;

      replace_symbol.insert(symbol_exprt{identifier, value.type()}, value);
      parameter_values.push_back(value);
    }

    if(p_it!=parameter_assignment.end())
    {
      error().source_location = p_it->source_location();
      error() << "too many parameter assignments" << eom;
      throw 0;
    }
  }
  
  return parameter_values;
}

/*******************************************************************\

Function: verilog_typecheckt::set_parameter_values

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::set_parameter_values(
  irept &module_source,
  const std::list<exprt> &parameter_values)
{
  auto p_it=parameter_values.begin();
  
  irept &module_items=module_source.add(ID_module_items);

  for(auto &module_item : module_items.get_sub())
    if(module_item.id() == ID_parameter_decl)
    {
      for(auto &decl : to_verilog_parameter_decl(module_item).declarations())
      {
        if(p_it!=parameter_values.end())
        {
          exprt &value = static_cast<exprt &>(decl.add(ID_value));
          value=*p_it;
          p_it++;
        }
      }
    }
}

/*******************************************************************\

Function: verilog_typecheckt::parameterize_module

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt verilog_typecheckt::parameterize_module(
  const source_locationt &location,
  const irep_idt &module_identifier,
  const exprt::operandst &parameter_assignments,
  const std::map<irep_idt, exprt> &instance_defparams)
{
  // No parameters assigned? Nothing to do.
  if(parameter_assignments.empty() && instance_defparams.empty())
    return module_identifier;

  // find base symbol
  
  symbol_tablet::symbolst::const_iterator it=
    symbol_table.symbols.find(module_identifier);
  
  if(it==symbol_table.symbols.end())
  {
    error().source_location=location;
    error() << "module not found" << eom;
    throw 0;
  }
  
  const symbolt &base_symbol=it->second;

  auto parameter_values = get_parameter_values(
    base_symbol.type.find(ID_module_source),
    parameter_assignments,
    instance_defparams);

  // create full instance symbol name
  std::string suffix="(";
  
  bool first=true;

  for(const auto &pv : parameter_values)
    if(pv.is_not_nil())
    {
      if(first) first=false; else suffix+=",";
      
      mp_integer i;
      if(to_integer_non_constant(pv, i))
      {
        error().source_location = pv.source_location();
        error() << "parameter expected to be constant, but got `"
                << to_string(pv) << "'" << eom;
        throw 0;
      } else
        suffix += i.to_ulong();
    }
    
  suffix+=')';

  irep_idt new_module_identifier=id2string(module_identifier)+suffix;
  
  if(symbol_table.symbols.find(new_module_identifier)!=
     symbol_table.symbols.end())
    return new_module_identifier; // done already
    
  // create symbol
  
  symbolt symbol(base_symbol);

  symbol.name=new_module_identifier;
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
    error().source_location=location;
    error() << "duplicate definition of parameterized module "
            << symbol.base_name << eom;
    throw 0;
  }

  // recursive call

  verilog_typecheckt verilog_typecheck(*new_symbol, symbol_table, get_message_handler());

  if(verilog_typecheck.typecheck_main())
    throw 0;

  return new_module_identifier;
}

