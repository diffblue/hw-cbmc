/*******************************************************************\

Module: Verilog Parameter Elaboration

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_typecheck.h"

/*******************************************************************\

Function: verilog_typecheckt::elaborate_parameters

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_parameters()
{
  // Parameters may depend on each other, in any order.
  // We traverse these dependencies recursively.
  // First collect all parameter declarators into the symbol table,
  // with type "to_be_elaborated".

  std::vector<irep_idt> to_be_elaborated;

  auto add_parameter = [this, &to_be_elaborated](
                         const verilog_parameter_declt::declaratort &declarator)
  {
    symbolt symbol;
    symbol.mode = mode;
    symbol.module = module_identifier;
    symbol.base_name = declarator.identifier();
    symbol.name = hierarchical_identifier(symbol.base_name);
    symbol.pretty_name = strip_verilog_prefix(symbol.name);
    symbol.is_macro = true;
    symbol.value = declarator.value();
    symbol.type = typet(ID_to_be_elaborated);
    symbol.location = declarator.source_location();

    auto result = symbol_table.insert(std::move(symbol));

    if(!result.second)
    {
      error().source_location = declarator.source_location();
      error() << "definition of symbol `" << declarator.identifier()
              << "\' conflicts with earlier definition at "
              << result.first.location << eom;
      throw 0;
    }

    to_be_elaborated.push_back(result.first.name);
  };

  // Gather the port declarations from the module source.
  auto &module_source =
    to_verilog_module_source(module_symbol.type.find(ID_module_source));

  for(auto &decl : module_source.parameter_port_list())
    add_parameter(decl);

  for(auto &item : module_source.module_items())
  {
    if(item.id() == ID_parameter_decl)
    {
      for(auto &decl : to_verilog_parameter_decl(item).declarations())
        add_parameter(decl);
    }
    else if(item.id() == ID_local_parameter_decl)
    {
      for(auto &decl : to_verilog_local_parameter_decl(item).declarations())
        add_parameter(decl);
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
    symbol.type = typet(ID_elaborating);

    convert_expr(symbol.value);
    symbol.value = elaborate_constant_expression(symbol.value);
    symbol.type = symbol.value.type();
  }
  else if(symbol.type.id() == ID_elaborating)
  {
    error().source_location = symbol.location;
    error() << "cyclic dependency when elaborating parameter "
            << symbol.display_name() << eom;
    throw 0;
  }
}
