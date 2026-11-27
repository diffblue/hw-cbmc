/*******************************************************************\

Module: Verilog Type Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/ebmc_util.h>
#include <util/replace_symbol.h>
#include <util/simplify_expr.h>

#include "typename.h"
#include "verilog_bind.h"
#include "verilog_expr.h"
#include "verilog_typecheck.h"

/*******************************************************************\

Function: verilog_typecheckt::get_parameter_declarators

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::vector<verilog_parameter_declt::declaratort>
verilog_typecheckt::get_parameter_declarators(
  const verilog_module_sourcet &module_source)
{
  std::vector<verilog_parameter_declt::declaratort> declarators;

  // We do the parameter ports first.
  const auto &parameter_port_decls = module_source.parameter_port_decls();

  for(auto &declaration : parameter_port_decls)
    for(auto &declarator : declaration.declarators())
      declarators.push_back(declarator);

  // We do the module item ports second.
  const auto &module_items = module_source.module_items();

  for(auto &item : module_items)
    if(item.id() == ID_parameter_decl)
      for(auto &declarator : to_verilog_parameter_decl(item).declarators())
        declarators.push_back(declarator);

  return declarators;
}

/*******************************************************************\

Function: verilog_typecheckt::get_parameter_values

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::list<exprt> verilog_typecheckt::get_parameter_values(
  const verilog_module_sourcet &module_source,
  const exprt::operandst &parameter_assignment,
  const std::map<irep_idt, exprt> &instance_defparams)
{
  const auto parameter_declarators = get_parameter_declarators(module_source);
  replace_symbolt replace_symbol;

  // 'nil' denotes 'not assigned'
  std::list<exprt> parameter_values;

  // Are the parameter values given with the instantiation
  // statement named or ordered?
  if(
    !parameter_assignment.empty() &&
    parameter_assignment.front().id() == ID_named_parameter_assignment)
  {
    // named
    std::map<irep_idt, exprt> map; // base name to values

    forall_expr(it, parameter_assignment)
    {
      irep_idt parameter = it->get(ID_parameter);
      map[parameter] = static_cast<const exprt &>(it->find(ID_value));
    }

    for(auto &decl : parameter_declarators)
    {
      auto &base_name = decl.base_name();

      exprt value = nil_exprt(); // "not assigned"

      if(map.find(base_name) != map.end())
        value = map[base_name];

      // Is there a defparam that overrides this parameter?
      auto def_param_it = instance_defparams.find(base_name);
      if(def_param_it != instance_defparams.end())
        value = def_param_it->second;

      parameter_values.push_back(value);
    }
  }
  else
  {
    // ordered
    exprt::operandst::const_iterator p_it = parameter_assignment.begin();

    for(auto &decl : parameter_declarators)
    {
      exprt value = nil_exprt();

      if(p_it != parameter_assignment.end())
      {
        value = *p_it;
        p_it++;
      }

      // Is there a defparam that overrides this parameter?
      auto &base_name = decl.base_name();
      auto def_param_it = instance_defparams.find(base_name);
      if(def_param_it != instance_defparams.end())
        value = def_param_it->second;

      parameter_values.push_back(value);
    }

    if(p_it != parameter_assignment.end())
    {
      throw errort().with_location(p_it->source_location())
        << "too many parameter assignments";
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
  verilog_module_sourcet &module_source,
  const source_locationt &instance_location,
  const std::list<exprt> &parameter_values)
{
  auto p_it = parameter_values.begin();

  auto &parameter_port_decls = module_source.parameter_port_decls();

  for(auto &declaration : parameter_port_decls)
    for(auto &declarator : declaration.declarators())
    {
      DATA_INVARIANT(
        p_it != parameter_values.end(), "have enough parameter values");

      // only overwrite when actually assigned
      if(p_it->is_not_nil())
        declarator.value() = *p_it;

      // check that we do have a value (the default value is optional)
      if(declarator.value().is_nil())
      {
        throw errort().with_location(instance_location)
          << "parameter port " << declarator.base_name() << " without value";
      }

      p_it++;
    }

  auto &module_items = module_source.module_items();

  for(auto &module_item : module_items)
    if(module_item.id() == ID_parameter_decl)
    {
      for(auto &declarator :
          to_verilog_parameter_decl(module_item).declarators())
      {
        if(p_it != parameter_values.end())
        {
          DATA_INVARIANT(
            p_it != parameter_values.end(), "have enough parameter values");

          // only overwrite when actually assigned
          if(p_it->is_not_nil())
            declarator.value() = *p_it;

          p_it++;
        }
      }
    }
}

/*******************************************************************\

Function: verilog_typecheckt::set_interface_port_types

  Inputs:

 Outputs:

 Purpose: An interface port is declared with the name of an interface,
          e.g., bus b, but not with its parameters, which are those of
          the interface instance that is bound to the port. The
          instantiation gives these as parameter assignments of the
          interface ports, which are set here on the declarations of
          the ports, in the same way as the values of parameters.

\*******************************************************************/

void verilog_typecheckt::set_interface_port_types(
  verilog_module_sourcet &module_source,
  const exprt::operandst &interface_port_assignments)
{
  if(interface_port_assignments.empty())
    return;

  std::map<irep_idt, irept> types;

  for(auto &assignment : interface_port_assignments)
    types[assignment.get(ID_parameter)] = assignment.find(ID_value);

  auto set_type = [&types](verilog_declt &decl)
  {
    if(decl.type().id() != ID_verilog_interface)
      return;

    // The interface ports have one declarator per declaration.
    for(auto &declarator : decl.declarators())
    {
      auto type_it = types.find(declarator.base_name());
      if(type_it != types.end())
        decl.type().add(ID_C_verilog_interface_type) = type_it->second;
    }
  };

  // the ANSI port declarations
  for(auto &decl : module_source.ports())
    set_type(decl);

  // the declarations of the interface ports in the body, for a design
  // element with a non-ANSI header
  for(auto &item : module_source.module_items())
    if(item.id() == ID_decl)
      set_type(to_verilog_decl(item));
}

/*******************************************************************\

Function: verilog_typecheckt::instantiate_design_element

  Inputs:

 Outputs:

 Purpose: Specialize a design element (module, interface, program, ...)
          to a given instance identifier and parameter assignment.

\*******************************************************************/

irep_idt verilog_typecheckt::instantiate_design_element(
  const source_locationt &location,
  const irep_idt &design_element_identifier,
  const irep_idt &design_element_base_name,
  const irep_idt &instance_identifier,
  const exprt::operandst &all_parameter_assignments,
  const std::map<irep_idt, exprt> &instance_defparams)
{
  // find the source symbol of the design element
  symbol_tablet::symbolst::const_iterator it =
    symbol_table.symbols.find(id2string(design_element_identifier) + "$source");

  if(it == symbol_table.symbols.end())
    throw errort().with_location(location)
      << "module `" << design_element_base_name << "' not found";

  const symbolt &source_symbol = it->second;

  // find the source
  const auto &module_source =
    to_verilog_module_source(source_symbol.type.find(ID_module_source));

  // The parameter assignments of the interface ports, which give the
  // interface types of the ports, are separate from those of the
  // parameters.
  exprt::operandst parameter_assignments, interface_port_assignments;

  for(auto &assignment : all_parameter_assignments)
  {
    if(assignment.id() == ID_verilog_interface_port_assignment)
      interface_port_assignments.push_back(assignment);
    else
      parameter_assignments.push_back(assignment);
  }

  auto parameter_values = get_parameter_values(
    module_source, parameter_assignments, instance_defparams);

  // Create the identifier of the parameterized design element
  // by appending "$module" to the identifier of the instance.
  auto new_design_element_identifier =
    id2string(instance_identifier) + "$module";

  DATA_INVARIANT(
    symbol_table.symbols.find(new_design_element_identifier) ==
      symbol_table.symbols.end(),
    "instantiated design element symbol must not yet exist");

  // copy the symbol
  symbolt symbol{source_symbol};

  symbol.name = new_design_element_identifier;
  symbol.module = new_design_element_identifier;
  symbol.type = typet{ID_module};

  // copy the module source
  verilog_module_sourcet source_copy = module_source;

  // apply any bind directives (1800-2017 23.11)
  apply_bind_directives(
    source_copy, source_symbol.base_name, instance_identifier, symbol_table);

  // set parameters
  set_parameter_values(source_copy, location, parameter_values);

  // set the interface types of the interface ports
  set_interface_port_types(source_copy, interface_port_assignments);

  // put symbol in symbol_table
  symbolt *new_symbol;

  bool move_return = symbol_table.move(symbol, new_symbol);
  CHECK_RETURN(!move_return);

  // recursive call

  verilog_typecheckt verilog_typecheck(
    standard, warn_implicit_nets, symbol_table, get_message_handler());

  verilog_typecheck.typecheck_design_element(
    source_copy, *new_symbol, instance_identifier);

  return new_design_element_identifier;
}
