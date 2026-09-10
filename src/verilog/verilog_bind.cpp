/*******************************************************************\

Module: Verilog bind Directives

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "verilog_bind.h"

#include <util/symbol_table_base.h>

#include <ebmc/ebmc_error.h>

#include "verilog_typecheck_base.h"

/// The identifier of the symbol that stores the bind directives.
/// The $ ensures that the identifier cannot clash with a module
/// identifier.
static irep_idt bind_directives_identifier()
{
  return "Verilog::$bind_directives";
}

std::string bind_target_as_string(const exprt &target)
{
  if(target.id() == ID_hierarchical_identifier)
  {
    auto &hierarchical_identifier = to_hierarchical_identifier_expr(target);
    return bind_target_as_string(hierarchical_identifier.module_instance()) +
           '.' + id2string(hierarchical_identifier.item().base_name());
  }
  else
    return id2string(to_verilog_identifier_expr(target).base_name());
}

irep_idt bind_target_instance_identifier(const exprt &target)
{
  return id2string(verilog_root_module_identifier()) + '.' +
         bind_target_as_string(target);
}

/// The symbol that stores the bind directives, created on demand.
/// The operands of the symbol value are the registered directives;
/// the "elaborated" named sub-irep records the base names of the
/// modules that have been elaborated.
static symbolt &bind_directives_symbol(symbol_table_baset &symbol_table)
{
  auto identifier = bind_directives_identifier();

  auto symbol_ptr = symbol_table.get_writeable(identifier);

  if(symbol_ptr != nullptr)
    return *symbol_ptr;

  symbolt symbol{identifier, typet{ID_verilog_bind_directives}, ID_Verilog};
  symbol.base_name = "$bind_directives";
  symbol.value = exprt{ID_verilog_bind_directives};

  auto result = symbol_table.insert(std::move(symbol));
  CHECK_RETURN(result.second);

  return result.first;
}

void register_bind_directive(
  const verilog_bind_directivet &bind_directive,
  symbol_table_baset &symbol_table)
{
  auto &symbol = bind_directives_symbol(symbol_table);

  // Registering the same directive again, e.g., when the design
  // element containing the directive is elaborated a second time,
  // has no effect.
  for(auto &op : symbol.value.operands())
    if(op.full_eq(bind_directive))
      return;

  auto &target = bind_directive.target();

  if(target.id() == ID_verilog_identifier)
  {
    auto base_name = to_verilog_identifier_expr(target).base_name();

    // Reject directives that bind a module to itself, which
    // would result in an unbounded recursion.
    if(bind_directive.instantiation().module_base_name() == base_name)
    {
      throw ebmc_errort{}.with_location(bind_directive.source_location())
        << "cannot bind module `" << base_name << "' to itself";
    }

    // The directive comes too late if an instance of the target
    // module has already been elaborated.
    if(symbol.value.find("elaborated").get_bool(base_name))
    {
      throw ebmc_errort{}.with_location(bind_directive.source_location())
        << "bind target `" << base_name << "' has already been elaborated";
    }
  }
  else
  {
    // The directive comes too late if the target instance has
    // already been elaborated.
    auto instance_identifier = bind_target_instance_identifier(target);
    auto module_identifier = id2string(instance_identifier) + "$module";

    if(symbol_table.lookup(module_identifier) != nullptr)
    {
      throw ebmc_errort{}.with_location(bind_directive.source_location())
        << "bind target `" << bind_target_as_string(target)
        << "' has already been elaborated";
    }
  }

  symbol.value.add_to_operands(bind_directive);
}

void apply_bind_directives(
  verilog_module_sourcet &module_source,
  const irep_idt &module_base_name,
  const irep_idt &instance_identifier,
  symbol_table_baset &symbol_table)
{
  auto &symbol = bind_directives_symbol(symbol_table);

  // Record the elaboration of this module, for detecting bind
  // directives that are registered too late.
  symbol.value.add("elaborated").set(module_base_name, 1);

  for(auto &op : symbol.value.operands())
  {
    auto &bind_directive = to_verilog_bind_directive(op);
    auto &target = bind_directive.target();

    bool matches;

    if(target.id() == ID_verilog_identifier)
    {
      // Module target: applies to all instances of the module.
      matches =
        to_verilog_identifier_expr(target).base_name() == module_base_name;
    }
    else
    {
      // Instance target: applies to the given instance only.
      matches = bind_target_instance_identifier(target) == instance_identifier;
    }

    if(matches)
    {
      // Add the instantiation to the target module, as if it
      // was written there.
      module_source.items().push_back(bind_directive.instantiation());
    }
  }
}

void check_bind_directives(const symbol_table_baset &symbol_table)
{
  auto symbol_ptr = symbol_table.lookup(bind_directives_identifier());

  if(symbol_ptr == nullptr)
    return; // no bind directives

  for(auto &op : symbol_ptr->value.operands())
  {
    auto &bind_directive = to_verilog_bind_directive(op);
    auto &target = bind_directive.target();

    if(target.id() == ID_verilog_identifier)
    {
      // The target module must exist.
      auto base_name = to_verilog_identifier_expr(target).base_name();
      auto source_identifier =
        id2string(verilog_module_symbol(base_name)) + "$source";

      if(symbol_table.lookup(source_identifier) == nullptr)
      {
        throw ebmc_errort{}.with_location(bind_directive.source_location())
          << "bind target `" << base_name << "' not found";
      }
    }
    else
    {
      // The target instance must exist in the elaborated hierarchy;
      // otherwise, the directive has not been applied.
      auto instance_identifier = bind_target_instance_identifier(target);
      auto instance_symbol_ptr = symbol_table.lookup(instance_identifier);

      if(
        instance_symbol_ptr == nullptr ||
        instance_symbol_ptr->type.id() != ID_verilog_module_instance)
      {
        throw ebmc_errort{}.with_location(bind_directive.source_location())
          << "bind target `" << bind_target_as_string(target) << "' not found";
      }
    }
  }
}
