/*******************************************************************\

Module: Verilog Elaboration

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/mathematical_types.h>

#include "verilog_typecheck.h"
#include "verilog_types.h"

void verilog_typecheckt::collect_port_symbols(const verilog_declt &decl)
{
  DATA_INVARIANT(decl.id() == ID_decl, "port declaration id");
  DATA_INVARIANT(
    decl.declarators().size() == 1,
    "port declarations must have one declarator");

  const auto &declarator = decl.declarators().front();

  const irep_idt &base_name = declarator.base_name();
  const irep_idt &port_class = decl.get_class();

  irep_idt identifier = hierarchical_identifier(base_name);

  if(port_class.empty())
  {
    // done when we see the proper declaration
  }
  else
  {
    // add the symbol
    typet type = convert_type(declarator.merged_type(decl.type()));

    symbolt new_symbol{identifier, type, mode};

    if(port_class == ID_input)
    {
      new_symbol.is_input = true;
    }
    else if(port_class == ID_output)
    {
      new_symbol.is_output = true;
    }
    else if(port_class == ID_output_register)
    {
      new_symbol.is_output = true;
      new_symbol.is_state_var = true;
    }
    else if(port_class == ID_inout)
    {
      new_symbol.is_input = true;
      new_symbol.is_output = true;
    }

    new_symbol.module = module_identifier;
    new_symbol.value.make_nil();
    new_symbol.base_name = base_name;
    new_symbol.pretty_name = strip_verilog_prefix(new_symbol.name);

    add_symbol(std::move(new_symbol));
  }
}

void verilog_typecheckt::collect_symbols(
  const typet &type,
  const verilog_parameter_declt::declaratort &declarator)
{
  // A localparam or parameter declarator.
  auto base_name = declarator.base_name();

  auto full_identifier = hierarchical_identifier(base_name);

  // If there's no type, parameters take the type of the
  // value. We signal this using the special type "derive_from_value".

  auto symbol_type =
    to_be_elaborated_typet(type.is_nil() ? derive_from_value_typet() : type);

  symbolt symbol{full_identifier, symbol_type, mode};

  symbol.module = module_identifier;
  symbol.base_name = base_name;
  symbol.pretty_name = strip_verilog_prefix(symbol.name);
  symbol.is_macro = true;
  symbol.value = declarator.value();
  symbol.location = declarator.source_location();

  add_symbol(std::move(symbol));
}

void verilog_typecheckt::collect_symbols(const typet &type)
{
  // These types are not yet converted.
  if(type.id() == ID_verilog_enum)
  {
    // These have a body, with enum constants, and an optional base type.
    const auto &enum_type = to_verilog_enum_type(type);

    if(enum_type.has_base_type())
      collect_symbols(enum_type.base_type());

    // The type needs to be converted later, as it may
    // depend on other elaboration-time constants.
    auto tbd_type = to_be_elaborated_typet(enum_type);

    // Add the enum names to the symbol table for subsequent elaboration.
    // Values are given, or the previous plus one, starting with value '0'.
    exprt initializer = from_integer(0, integer_typet());

    for(auto &enum_name : enum_type.enum_names())
    {
      // The initializer will also be converted later.
      if(enum_name.value().is_not_nil())
        initializer = enum_name.value();

      exprt value = typecast_exprt(initializer, tbd_type);
      value.add_source_location() = enum_name.source_location();

      const auto base_name = enum_name.base_name();
      const auto identifier = hierarchical_identifier(base_name);
      symbolt enum_name_symbol(identifier, tbd_type, mode);
      enum_name_symbol.pretty_name =
        strip_verilog_prefix(enum_name_symbol.name);
      enum_name_symbol.module = module_identifier;
      enum_name_symbol.base_name = base_name;
      enum_name_symbol.value = std::move(value);
      enum_name_symbol.is_macro = true;
      enum_name_symbol.is_file_local = true;
      enum_name_symbol.location = enum_name.source_location();
      add_symbol(std::move(enum_name_symbol));

      initializer = plus_exprt(
        typecast_exprt(initializer, tbd_type),
        typecast_exprt(from_integer(1, integer_typet()), tbd_type));
    }

    // Add a symbol for the enum to the symbol table.
    // This allows looking up the enum name identifiers.
    {
      auto identifier = enum_type.identifier();
      type_symbolt enum_type_symbol(identifier, enum_type, mode);
      enum_type_symbol.module = module_identifier;
      enum_type_symbol.is_file_local = true;
      enum_type_symbol.location = enum_type.source_location();
      add_symbol(std::move(enum_type_symbol));
    }
  }
}

void verilog_typecheckt::collect_symbols(const verilog_declt &decl)
{
  // There may be symbols in the type (say an enum).
  collect_symbols(decl.type());

  const auto decl_class = decl.get_class();

  // Typedef?
  if(decl_class == ID_typedef)
  {
    for(auto &declarator : decl.declarators())
    {
      DATA_INVARIANT(declarator.id() == ID_declarator, "must have declarator");

      auto base_name = declarator.base_name();
      auto full_identifier = hierarchical_identifier(base_name);

      symbolt symbol{
        full_identifier, to_be_elaborated_typet(decl.type()), mode};

      symbol.module = module_identifier;
      symbol.base_name = base_name;
      symbol.pretty_name = strip_verilog_prefix(symbol.name);
      symbol.is_macro = true;
      symbol.is_type = true;
      symbol.location = declarator.source_location();
      symbol.value = nil_exprt();

      add_symbol(std::move(symbol));
    }
  }
  else if(
    decl_class == ID_input || decl_class == ID_output ||
    decl_class == ID_output_register || decl_class == ID_inout)
  {
    // If these are inputs/outputs of a function/task, then
    // adjust the function/task signature.
    if(function_or_task_name.empty())
    {
      symbolt symbol;

      symbol.mode = mode;
      symbol.module = module_identifier;
      symbol.value.make_nil();

      if(decl_class == ID_input)
        symbol.is_input = true;
      else if(decl_class == ID_output)
        symbol.is_output = true;
      else if(decl_class == ID_output_register)
      {
        symbol.is_output = true;
        symbol.is_state_var = true;
      }
      else if(decl_class == ID_inout)
      {
        symbol.is_input = true;
        symbol.is_output = true;
      }

      for(auto &declarator : decl.declarators())
      {
        DATA_INVARIANT(
          declarator.id() == ID_declarator, "must have declarator");

        symbol.base_name = declarator.base_name();
        symbol.location = declarator.source_location();
        symbol.type = convert_type(declarator.merged_type(decl.type()));

        if(symbol.base_name.empty())
        {
          throw errort().with_location(decl.source_location())
            << "empty symbol name";
        }

        symbol.name = hierarchical_identifier(symbol.base_name);
        symbol.pretty_name = strip_verilog_prefix(symbol.name);

        auto result = symbol_table.get_writeable(symbol.name);

        if(result == nullptr)
        {
          symbol_table.add(symbol);
        }
        else
        {
          symbolt &osymbol = *result;

          if(symbol.type != osymbol.type)
          {
            if(get_width(symbol.type) > get_width(osymbol.type))
              osymbol.type = symbol.type;
          }

          osymbol.is_input = symbol.is_input || osymbol.is_input;
          osymbol.is_output = symbol.is_output || osymbol.is_output;
          osymbol.is_state_var = symbol.is_state_var || osymbol.is_state_var;

          // a register can't be an input as well
          if(osymbol.is_input && osymbol.is_state_var)
          {
            throw errort().with_location(declarator.source_location())
              << "port `" << symbol.base_name
              << "' is declared both as input and as register";
          }
        }

        symbols_added.push_back(symbol.name);
      }
    }
    else
    {
      symbolt symbol;
      bool input = false, output = false;

      symbol.mode = mode;
      symbol.module = module_identifier;
      symbol.value.make_nil();

      symbol.is_state_var = true;

      if(decl_class == ID_input)
      {
        input = true;
      }
      else if(decl_class == ID_output)
      {
        output = true;
      }
      else if(decl_class == ID_output_register)
      {
        output = true;
      }
      else if(decl_class == ID_inout)
      {
        input = true;
        output = true;
      }

      for(auto &declarator : decl.declarators())
      {
        DATA_INVARIANT(
          declarator.id() == ID_declarator, "must have declarator");

        symbol.base_name = declarator.base_name();

        if(symbol.base_name.empty())
        {
          throw errort().with_location(decl.source_location())
            << "empty symbol name";
        }

        symbol.type = convert_type(declarator.merged_type(decl.type()));
        symbol.name = hierarchical_identifier(symbol.base_name);
        symbol.pretty_name = strip_verilog_prefix(symbol.name);

        if(input || output)
        {
          // Terminology clash: these aren't called 'parameters'
          // in Verilog terminology, but inputs and outputs.
          // We'll use the C terminology, and call them parameters.
          // Not to be confused with module parameters.
          symbolt &function_or_task_symbol =
            symbol_table.get_writeable_ref(function_or_task_name);
          code_typet::parameterst &parameters =
            to_code_type(function_or_task_symbol.type).parameters();
          parameters.push_back(code_typet::parametert(symbol.type));
          code_typet::parametert &parameter = parameters.back();
          parameter.set_base_name(symbol.base_name);
          parameter.set_identifier(symbol.name);
          parameter.set(ID_output, output);
          parameter.set(ID_input, input);
        }

        auto result = symbol_table.symbols.find(symbol.name);

        if(result != symbol_table.symbols.end())
        {
          throw errort().with_location(decl.source_location())
            << "symbol `" << symbol.base_name << "' is already declared";
        }

        symbol_table.add(symbol);
      }
    }
  }
  else if(decl_class == ID_verilog_genvar)
  {
    symbolt symbol{irep_idt{}, verilog_genvar_typet{}, mode};

    symbol.module = module_identifier;
    symbol.value.make_nil();

    for(auto &declarator : decl.declarators())
    {
      DATA_INVARIANT(declarator.id() == ID_declarator, "must have declarator");

      symbol.base_name = declarator.base_name();
      symbol.location = declarator.source_location();

      if(symbol.base_name.empty())
        throw errort().with_location(decl.source_location())
          << "empty symbol name";

      symbol.name = hierarchical_identifier(symbol.base_name);
      symbol.pretty_name = strip_verilog_prefix(symbol.name);

      genvars[symbol.base_name] = -1;

      add_symbol(symbol);
    }
  }
  else if(
    decl_class == ID_wire || decl_class == ID_supply0 ||
    decl_class == ID_supply1 || decl_class == ID_triand ||
    decl_class == ID_trior || decl_class == ID_trireg ||
    decl_class == ID_tri0 || decl_class == ID_tri1 || decl_class == ID_uwire ||
    decl_class == ID_wire || decl_class == ID_wand || decl_class == ID_wor)
  {
    symbolt symbol;

    symbol.mode = mode;
    symbol.module = module_identifier;
    symbol.value = nil_exprt();

    for(auto &declarator : decl.declarators())
    {
      DATA_INVARIANT(declarator.id() == ID_declarator, "must have declarator");

      symbol.base_name = declarator.base_name();
      symbol.location = declarator.source_location();
      symbol.type = convert_type(declarator.merged_type(decl.type()));

      if(symbol.base_name.empty())
      {
        throw errort().with_location(decl.source_location());
        error() << "empty symbol name" << eom;
      }

      symbol.name = hierarchical_identifier(symbol.base_name);
      symbol.pretty_name = strip_verilog_prefix(symbol.name);

      auto result = symbol_table.get_writeable(symbol.name);

      if(result == nullptr)
      {
        // new identifier
        symbol_table.add(symbol);
      }
      else
      {
        // We have an existing symbol with that name.
        // This is ok for certain symbols, e.g., input/wire, output/reg.
        symbolt &osymbol = *result;

        if(osymbol.type.id() == ID_code)
        {
          throw errort().with_location(decl.source_location())
            << "symbol `" << symbol.base_name << "' is already declared";
        }

        // change of type?
        if(symbol.type != osymbol.type)
        {
          if(get_width(symbol.type) > get_width(osymbol.type))
            osymbol.type = symbol.type;
        }
      }

      symbols_added.push_back(symbol.name);
    }
  }
  else if(decl_class == ID_reg || decl_class == ID_var)
  {
    symbolt symbol;

    symbol.mode = mode;
    symbol.module = module_identifier;
    symbol.value = nil_exprt();
    symbol.is_state_var = true;

    for(auto &declarator : decl.declarators())
    {
      DATA_INVARIANT(declarator.id() == ID_declarator, "must have declarator");

      symbol.base_name = declarator.base_name();
      symbol.location = declarator.source_location();
      symbol.type = convert_type(declarator.merged_type(decl.type()));

      if(symbol.base_name.empty())
      {
        throw errort().with_location(decl.source_location())
          << "empty symbol name";
      }

      symbol.name = hierarchical_identifier(symbol.base_name);
      symbol.pretty_name = strip_verilog_prefix(symbol.name);

      auto result = symbol_table.get_writeable(symbol.name);

      if(result == nullptr)
      {
        symbol_table.add(symbol);
      }
      else
      {
        symbolt &osymbol = *result;

        if(osymbol.type.id() == ID_code)
        {
          throw errort().with_location(decl.source_location())
            << "symbol `" << symbol.base_name << "' is already declared";
        }

        if(symbol.type != osymbol.type)
        {
          if(get_width(symbol.type) > get_width(osymbol.type))
            osymbol.type = symbol.type;
        }

        osymbol.is_input = symbol.is_input || osymbol.is_input;
        osymbol.is_output = symbol.is_output || osymbol.is_output;
        osymbol.is_state_var = symbol.is_state_var || osymbol.is_state_var;

        // a register can't be an input as well
        if(osymbol.is_input && osymbol.is_state_var)
        {
          throw errort().with_location(decl.source_location())
            << "symbol `" << symbol.base_name
            << "' is declared both as input and as register";
        }
      }

      symbols_added.push_back(symbol.name);
    }
  }
  else if(decl_class == ID_function || decl_class == ID_task)
  {
    typet return_type;

    if(decl_class == ID_function)
      return_type = convert_type(decl.type());
    else
      return_type = empty_typet();

    auto base_name = decl.get_identifier();
    auto identifier = hierarchical_identifier(base_name);
    symbolt symbol{identifier, code_typet{{}, std::move(return_type)}, mode};

    symbol.base_name = base_name;
    symbol.location = decl.source_location();
    symbol.pretty_name = strip_verilog_prefix(symbol.name);
    symbol.module = module_identifier;
    symbol.value = decl;

    add_symbol(symbol);

    function_or_task_name = symbol.name;

    // do the ANSI-style ports, if applicable
    for(auto &port_decl : decl.ports())
    {
      // These must have one declarator exactly.
      DATA_INVARIANT(
        port_decl.declarators().size() == 1, "must have one port declarator");
      collect_symbols(port_decl); // rec. call
    }

    // add a symbol for the return value of functions, if applicable

    if(decl_class == ID_function)
    {
      symbolt return_symbol;
      return_symbol.is_state_var = true;
      return_symbol.is_lvalue = true;
      return_symbol.mode = symbol.mode;
      return_symbol.module = symbol.module;
      return_symbol.base_name = symbol.base_name;
      return_symbol.value = nil_exprt();
      return_symbol.type = to_code_type(symbol.type).return_type();

      return_symbol.name =
        id2string(symbol.name) + "." + id2string(symbol.base_name);

      return_symbol.pretty_name = strip_verilog_prefix(return_symbol.name);

      symbol_table.add(return_symbol);
    }

    // collect symbols in the declarations within the task/function
    for(auto &decl : decl.declarations())
      collect_symbols(decl);

    collect_symbols(decl.body());

    function_or_task_name = "";
  }
  else
  {
    DATA_INVARIANT(false, "unexpected decl class " + id2string(decl_class));
  }
}

#include <iostream>

void verilog_typecheckt::collect_symbols(const verilog_lett &let)
{
  // These have one declarator.
  auto &declarator = let.declarator();

  // We don't currently do let ports
  if(declarator.type().is_not_nil())
  {
    throw errort().with_location(let.source_location())
      << "let ports not supported yet";
  }

  const irep_idt &base_name = declarator.base_name();
  irep_idt identifier = hierarchical_identifier(base_name);

  // The range type is always derived from the type of the
  // value expression.
  auto type = to_be_elaborated_typet(derive_from_value_typet());

  // add the symbol
  symbolt new_symbol(identifier, type, mode);

  new_symbol.module = module_identifier;
  new_symbol.is_macro = true;
  new_symbol.value = declarator.value();
  new_symbol.base_name = base_name;
  new_symbol.pretty_name = strip_verilog_prefix(new_symbol.name);

  add_symbol(std::move(new_symbol));
}

void verilog_typecheckt::collect_symbols(const verilog_statementt &statement)
{
  if(statement.id() == ID_assert || statement.id() == ID_assume)
  {
  }
  else if(
    statement.id() == ID_verilog_assert_property ||
    statement.id() == ID_verilog_assume_property ||
    statement.id() == ID_verilog_cover_property)
  {
  }
  else if(
    statement.id() == ID_verilog_smv_assert ||
    statement.id() == ID_verilog_smv_assume)
  {
  }
  else if(statement.id() == ID_block)
  {
    // These may be named
    auto &block_statement = to_verilog_block(statement);

    if(block_statement.is_named())
      enter_named_block(block_statement.base_name());

    for(auto &block_statement : to_verilog_block(statement).operands())
      collect_symbols(to_verilog_statement(block_statement));

    if(block_statement.is_named())
      named_blocks.pop_back();
  }
  else if(statement.id() == ID_blocking_assign)
  {
  }
  else if(
    statement.id() == ID_case || statement.id() == ID_casex ||
    statement.id() == ID_casez)
  {
    auto &case_statement = to_verilog_case_base(statement);

    for(std::size_t i = 1; i < case_statement.operands().size(); i++)
    {
      const verilog_case_itemt &c =
        to_verilog_case_item(statement.operands()[i]);

      collect_symbols(c.case_statement());
    }
  }
  else if(statement.id() == ID_decl)
  {
    collect_symbols(to_verilog_decl(statement));
  }
  else if(statement.id() == ID_delay)
  {
    collect_symbols(to_verilog_delay(statement).body());
  }
  else if(statement.id() == ID_event_guard)
  {
    collect_symbols(to_verilog_event_guard(statement).body());
  }
  else if(statement.id() == ID_for)
  {
    collect_symbols(to_verilog_for(statement).body());
  }
  else if(statement.id() == ID_forever)
  {
    collect_symbols(to_verilog_forever(statement).body());
  }
  else if(statement.id() == ID_function_call)
  {
  }
  else if(statement.id() == ID_if)
  {
    auto &if_statement = to_verilog_if(statement);
    collect_symbols(if_statement.then_case());
    if(if_statement.has_else_case())
      collect_symbols(if_statement.else_case());
  }
  else if(statement.id() == ID_non_blocking_assign)
  {
  }
  else if(
    statement.id() == ID_postincrement || statement.id() == ID_postdecrement ||
    statement.id() == ID_preincrement || statement.id() == ID_predecrement)
  {
  }
  else if(statement.id() == ID_skip)
  {
  }
  else if(statement.id() == ID_verilog_label_statement)
  {
    collect_symbols(to_verilog_label_statement(statement).statement());
  }
  else if(statement.id() == ID_procedural_continuous_assign)
  {
  }
  else
    DATA_INVARIANT(false, "unexpected statement: " + statement.id_string());
}

void verilog_typecheckt::collect_symbols(
  const verilog_module_itemt &module_item)
{
  if(module_item.id() == ID_parameter_decl)
  {
    auto &parameter_decl = to_verilog_parameter_decl(module_item);
    collect_symbols(parameter_decl.type());
    for(auto &decl : parameter_decl.declarations())
      collect_symbols(parameter_decl.type(), decl);
  }
  else if(module_item.id() == ID_local_parameter_decl)
  {
    auto &localparam_decl = to_verilog_local_parameter_decl(module_item);
    collect_symbols(localparam_decl.type());
    for(auto &decl : localparam_decl.declarations())
      collect_symbols(localparam_decl.type(), decl);
  }
  else if(module_item.id() == ID_decl)
  {
    collect_symbols(to_verilog_decl(module_item));
  }
  else if(
    module_item.id() == ID_verilog_always ||
    module_item.id() == ID_verilog_always_comb ||
    module_item.id() == ID_verilog_always_ff ||
    module_item.id() == ID_verilog_always_latch)
  {
    collect_symbols(to_verilog_always_base(module_item).statement());
  }
  else if(module_item.id() == ID_initial)
  {
    collect_symbols(to_verilog_initial(module_item).statement());
  }
  else if(
    module_item.id() == ID_generate_block ||
    module_item.id() == ID_generate_for || module_item.id() == ID_generate_if)
  {
    // postpone until constants are elaborated
  }
  else if(module_item.id() == ID_inst)
  {
    // these symbols are currently created in verilog_interfaces
  }
  else if(module_item.id() == ID_inst_builtin)
  {
    // these symbols are currently created in verilog_interfaces
  }
  else if(module_item.id() == ID_continuous_assign)
  {
  }
  else if(
    module_item.id() == ID_verilog_assert_property ||
    module_item.id() == ID_verilog_assume_property ||
    module_item.id() == ID_verilog_cover_property)
  {
  }
  else if(module_item.id() == ID_parameter_override)
  {
  }
  else if(module_item.id() == ID_set_genvars)
  {
    collect_symbols(to_verilog_set_genvars(module_item).module_item());
  }
  else if(module_item.id() == ID_verilog_final)
  {
  }
  else if(module_item.id() == ID_verilog_let)
  {
    collect_symbols(to_verilog_let(module_item));
  }
  else if(module_item.id() == ID_verilog_empty_item)
  {
  }
  else
    DATA_INVARIANT(false, "unexpected module item: " + module_item.id_string());
}

verilog_typecheckt::module_itemst
verilog_typecheckt::elaborate_level(const module_itemst &module_items)
{
  // Gather the symbols in the given module items.
  for(auto &module_item : module_items)
    collect_symbols(module_item);

  // Now elaborate the symbols we found.
  // This refers to "elaboration-time constants" as defined
  // in System Verilog 1800-2017, and includes
  // * parameters (including parameter ports)
  // * localparam
  // * specparam
  // * enum constants
  //
  // These may depend on each other, in any order.
  // We traverse these dependencies recursively.
  for(auto identifier : symbols_added)
    elaborate_symbol_rec(identifier);

  // Now that we know parameters and other constants,
  // process the generate constructs at this level, if any.
  // This may yield new module items, which are elaborated
  // recursively.
  module_itemst result;

  for(auto &module_item : module_items)
  {
    if(module_item.id() == ID_generate_block)
    {
      // elaborate_generate_item calls elaborate_level
      // recursively.
      auto generated_items = elaborate_generate_item(module_item);
      result.insert(
        result.end(), generated_items.begin(), generated_items.end());
    }
    else
      result.push_back(module_item);
  }

  return result;
}

void verilog_typecheckt::add_symbol(symbolt symbol)
{
  auto location = symbol.location;
  auto result = symbol_table.insert(std::move(symbol));

  if(!result.second)
  {
    throw errort().with_location(location)
      << "definition of symbol `" << symbol.base_name
      << "' conflicts with earlier definition at line "
      << result.first.location.get_line();
  }

  symbols_added.push_back(result.first.name);
}

verilog_module_exprt
verilog_typecheckt::elaborate(const verilog_module_sourcet &module_source)
{
  // IEEE 1800-2017 23.10.4.1 Order of elaboration
  // This section suggests alternating between parameter evaluation
  // and the expansion of generate blocks.

  // At the top level of the module, include the parameter ports.
  for(auto &parameter_port_decl : module_source.parameter_port_list())
    collect_symbols(typet(ID_nil), parameter_port_decl);

  // At the top level of the module, include the non-parameter module port
  // module items.
  for(auto &port_decl : module_source.ports())
    collect_port_symbols(port_decl);

  // Now elaborate the top level of the module.
  auto elaborated_module_items = elaborate_level(module_source.module_items());

  // Create verilog_module expression from the elaborated
  // module items.
  return verilog_module_exprt(std::move(elaborated_module_items));
}

void verilog_typecheckt::elaborate_symbol_rec(irep_idt identifier)
{
  auto &symbol = *symbol_table.get_writeable(identifier);

  // Does the still need to be elaborated?
  if(symbol.type.id() == ID_to_be_elaborated)
  {
    // mark as "elaborating" to detect cycles
    symbol.type.id(ID_elaborating);

    // Is the type derived from the value (e.g., parameters)?
    if(to_type_with_subtype(symbol.type).subtype().id() == ID_derive_from_value)
    {
      // First elaborate the value, possibly recursively.
      convert_expr(symbol.value);
      symbol.value = elaborate_constant_expression(symbol.value);
      symbol.type = symbol.value.type();
    }
    else
    {
      // No, elaborate the type.
      auto elaborated_type =
        convert_type(to_type_with_subtype(symbol.type).subtype());
      symbol.type = elaborated_type;

      // Now elaborate the value, possibly recursively, if any.
      if(symbol.value.is_not_nil())
      {
        convert_expr(symbol.value);
        symbol.value = elaborate_constant_expression(symbol.value);

        // Cast to the given type.
        propagate_type(symbol.value, symbol.type);
      }
    }
  }
  else if(symbol.type.id() == ID_elaborating)
  {
    throw errort().with_location(symbol.location)
      << "cyclic dependency when elaborating " << symbol.display_name();
  }
}
