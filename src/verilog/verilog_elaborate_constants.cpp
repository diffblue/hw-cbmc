/*******************************************************************\

Module: Verilog Elaboration

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/mathematical_types.h>

#include "verilog_typecheck.h"
#include "verilog_types.h"

void verilog_typecheckt::collect_symbols(
  const typet &type,
  const verilog_parameter_declt::declaratort &declarator)
{
  // A localparam or parameter declarator.
  auto base_name = declarator.identifier();

  auto full_identifier =
    id2string(module_identifier) + "." + id2string(base_name);

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

    // The default base type is 'int'.
    auto base_type =
      enum_type.has_base_type() ? enum_type.base_type() : signedbv_typet(32);

    // Add the enum names to the symbol table for subsequent elaboration.
    // Values are given, or the previous plus one, starting with value '0'.
    exprt initializer = from_integer(0, integer_typet());

    for(auto &enum_name : enum_type.enum_names())
    {
      if(enum_name.value().is_not_nil())
        initializer = enum_name.value();

      exprt value = typecast_exprt(initializer, base_type);

      symbolt enum_name_symbol(enum_name.identifier(), base_type, mode);
      enum_name_symbol.module = module_identifier;
      enum_name_symbol.base_name = enum_name.base_name();
      enum_name_symbol.value = std::move(value);
      enum_name_symbol.is_macro = true;
      enum_name_symbol.is_file_local = true;
      add_symbol(std::move(enum_name_symbol));

      initializer = plus_exprt(
        typecast_exprt(initializer, base_type),
        typecast_exprt(from_integer(1, integer_typet()), base_type));
    }
  }
}

void verilog_typecheckt::collect_symbols(const verilog_declt &decl)
{
  // There may be symbols in the type (say an enum).
  collect_symbols(decl.type());

  const auto decl_class = decl.get_class();

  if(decl_class == ID_function || decl_class == ID_task)
  {
    symbolt tf_symbol;

    tf_symbol.mode = mode;
    tf_symbol.module = module_identifier;
    tf_symbol.value = decl;

    typet return_type;

    if(decl_class == ID_function)
      return_type = to_be_elaborated_typet(decl.type());
    else
      return_type = empty_typet();

    tf_symbol.type = code_typet{{}, return_type};

    tf_symbol.base_name = decl.get_identifier();
    tf_symbol.name = hierarchical_identifier(tf_symbol.base_name);
    tf_symbol.pretty_name = strip_verilog_prefix(tf_symbol.name);

    function_or_task_name = tf_symbol.name;

    add_symbol(tf_symbol); // copy

    // add a symbol for the return value of functions
    if(decl_class == ID_function)
    {
      symbolt return_symbol;
      return_symbol.is_state_var = true;
      return_symbol.is_lvalue = true;
      return_symbol.mode = mode;
      return_symbol.module = module_identifier;
      return_symbol.base_name = tf_symbol.base_name;
      return_symbol.value.make_nil();
      return_symbol.type = to_code_type(tf_symbol.type).return_type();

      return_symbol.name =
        id2string(tf_symbol.name) + "." + id2string(tf_symbol.base_name);

      return_symbol.pretty_name = strip_verilog_prefix(return_symbol.name);

      add_symbol(std::move(return_symbol));
    }

    // do the declarations within the task/function
    for(auto &decl : decl.declarations())
      collect_symbols(decl);

    collect_symbols(decl.body());

    function_or_task_name = "";
    return;
  }

  // Typedef?
  if(decl_class == ID_typedef)
  {
    for(auto &declarator : decl.operands())
    {
      auto symbol_expr = [](const exprt &declarator) -> const symbol_exprt & {
        if(declarator.id() == ID_symbol)
          return to_symbol_expr(declarator);
        else if(
          declarator.id() == ID_equal &&
          to_equal_expr(declarator).lhs().id() == ID_symbol)
          return to_symbol_expr(to_equal_expr(declarator).lhs());
        else
          DATA_INVARIANT(false, "failed to find symbol in declarator");
      }(declarator);

      auto base_name = symbol_expr.get_identifier();

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
}

void verilog_typecheckt::collect_symbols(const verilog_statementt &statement)
{
  if(statement.id() == ID_assert || statement.id() == ID_assume)
  {
  }
  else if(statement.id() == ID_block)
  {
    // These may be named
    auto &block_statement = to_verilog_block(statement);

    if(block_statement.is_named())
      enter_named_block(block_statement.identifier());

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
  else if(module_item.id() == ID_always)
  {
    collect_symbols(to_verilog_always(module_item).statement());
  }
  else if(module_item.id() == ID_initial)
  {
    collect_symbols(to_verilog_initial(module_item).statement());
  }
  else if(module_item.id() == ID_generate_block)
  {
  }
  else if(module_item.id() == ID_inst || module_item.id() == ID_inst_builtin)
  {
  }
  else if(module_item.id() == ID_continuous_assign)
  {
  }
  else if(module_item.id() == ID_assert || module_item.id() == ID_assume)
  {
  }
  else if(module_item.id() == ID_parameter_override)
  {
  }
  else
    DATA_INVARIANT(false, "unexpected module item: " + module_item.id_string());
}

void verilog_typecheckt::collect_symbols(
  const verilog_module_sourcet &module_source)
{
  // Gather the parameter port declarations from the module source.
  for(auto &parameter_port_decl : module_source.parameter_port_list())
    collect_symbols(typet(ID_nil), parameter_port_decl);

  // Gather the symbols in the module body.
  for(auto &module_item : module_source.module_items())
    collect_symbols(module_item);
}

void verilog_typecheckt::add_symbol(symbolt symbol)
{
  auto result = symbol_table.insert(std::move(symbol));

  if(!result.second)
  {
    throw errort().with_location(symbol.location)
      << "definition of symbol `" << symbol.base_name
      << "\' conflicts with earlier definition at " << result.first.location;
  }

  symbols_added.push_back(result.first.name);
}

void verilog_typecheckt::elaborate()
{
  // First find the symbols in the module source.
  auto &module_source =
    to_verilog_module_source(module_symbol.type.find(ID_module_source));

  // Then collect all constant identifiers into the symbol table,
  // with type "to_be_elaborated".
  collect_symbols(module_source);

  // Now elaborate the types of the symbols we found.
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
    elaborate_rec(identifier);
}

void verilog_typecheckt::elaborate_rec(irep_idt identifier)
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
    error().source_location = symbol.location;
    error() << "cyclic dependency when elaborating " << symbol.display_name()
            << eom;
    throw 0;
  }
}
