/*******************************************************************\

Module: Verilog Elaboration Time Constants

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_typecheck.h"

/*******************************************************************\

Function: verilog_typecheckt::elaborate_constants

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_constants()
{
  // This refers to "elaboration-time constants" as defined
  // in System Verilog 1800-2017, and includes
  // * parameters (including parameter ports)
  // * localparam
  // * specparam
  // * enum constants
  //
  // These may depend on each other, in any order.
  // We traverse these dependencies recursively.
  // First collect all constant identifiers into the symbol table,
  // with type "to_be_elaborated".

  std::vector<irep_idt> to_be_elaborated;

  auto add_parameter =
    [this, &to_be_elaborated](
      const typet &type,
      const verilog_parameter_declt::declaratort &declarator) {
      symbolt symbol{
        hierarchical_identifier(declarator.identifier()),
        type_with_subtypet(ID_to_be_elaborated, type),
        mode};

      symbol.module = module_identifier;
      symbol.base_name = declarator.identifier();
      symbol.pretty_name = strip_verilog_prefix(symbol.name);
      symbol.is_macro = true;
      symbol.value = declarator.value();
      symbol.location = declarator.source_location();

      auto result = symbol_table.insert(std::move(symbol));

      if(!result.second)
      {
        throw errort().with_location(declarator.source_location())
          << "definition of symbol `" << declarator.identifier()
          << "\' conflicts with earlier definition at "
          << result.first.location;
      }

      to_be_elaborated.push_back(result.first.name);
    };

  // Gather the port declarations from the module source.
  auto &module_source =
    to_verilog_module_source(module_symbol.type.find(ID_module_source));

  for(auto &decl : module_source.parameter_port_list())
    add_parameter(typet(ID_nil), decl);

  for(auto &item : module_source.module_items())
  {
    if(item.id() == ID_parameter_decl)
    {
      auto &parameter_decl = to_verilog_parameter_decl(item);
      for(auto &decl : parameter_decl.declarations())
        add_parameter(parameter_decl.type(), decl);
    }
    else if(item.id() == ID_local_parameter_decl)
    {
      auto &localparam_decl = to_verilog_local_parameter_decl(item);
      for(auto &decl : localparam_decl.declarations())
        add_parameter(localparam_decl.type(), decl);
    }
  }

  // Iterate over all parameters, to make sure all are elborated.
  for(auto &symbol_name : to_be_elaborated)
    elaborate_parameter(symbol_name);
}

/*******************************************************************\

Function: verilog_typecheckt::elaborate_parameter

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_parameter(irep_idt identifier)
{
  auto &symbol = *symbol_table.get_writeable(identifier);

  // Does it still need to be elaborated?
  if(symbol.type.id() == ID_to_be_elaborated)
  {
    // mark as "elaborating" to detect cycles
    symbol.type.id(ID_elaborating);

    // first elaborate the value
    convert_expr(symbol.value);
    symbol.value = elaborate_constant_expression(symbol.value);

    // Now elaborate the type. It may be given or implicit.
    if(to_type_with_subtype(symbol.type).subtype().is_nil())
    {
      // It's implicit. Use type of value.
      symbol.type = symbol.value.type();
    }
    else
    {
      // It's given. Elaborate it, then cast value.
      auto elaborated_type =
        convert_type(to_type_with_subtype(symbol.type).subtype());
      symbol.type = elaborated_type;
      propagate_type(symbol.value, symbol.type);
    }
  }
  else if(symbol.type.id() == ID_elaborating)
  {
    error().source_location = symbol.location;
    error() << "cyclic dependency when elaborating parameter "
            << symbol.display_name() << eom;
    throw 0;
  }
}
