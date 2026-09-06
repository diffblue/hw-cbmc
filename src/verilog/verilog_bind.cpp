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

/// The base name of the bind target, for error messages.
/// E.g., main.sub.s for an instance target.
static std::string bind_target_as_string(const exprt &target)
{
  if(target.id() == ID_hierarchical_identifier)
  {
    auto &binary = to_binary_expr(target);
    return bind_target_as_string(binary.op0()) + '.' +
           id2string(binary.op1().get(ID_base_name));
  }
  else
    return id2string(target.get(ID_base_name));
}

/// The elaborated identifier of an instance target,
/// e.g., Verilog::$root.main.sub.s
static irep_idt bind_target_instance_identifier(const exprt &target)
{
  return id2string(verilog_root_module_identifier()) + '.' +
         bind_target_as_string(target);
}

std::vector<verilog_bind_directivet>
collect_bind_directives(std::list<verilog_parse_treet> &parse_trees)
{
  std::vector<verilog_bind_directivet> bind_directives;

  for(auto &parse_tree : parse_trees)
  {
    for(auto item_it = parse_tree.items.begin();
        item_it != parse_tree.items.end();) // no it++
    {
      if(item_it->id() == ID_verilog_bind_directive)
      {
        bind_directives.push_back(
          to_verilog_bind_directive(static_cast<exprt &>(*item_it)));
        item_it = parse_tree.items.erase(item_it);
      }
      else
      {
        // Bind directives may also be module items.
        if(
          item_it->id() == ID_verilog_module ||
          item_it->id() == ID_verilog_checker ||
          item_it->id() == ID_verilog_interface)
        {
          auto &container = static_cast<verilog_item_containert &>(*item_it);
          auto &items = container.items();

          for(auto it = items.begin(); it != items.end();) // no it++
          {
            if(it->id() == ID_verilog_bind_directive)
            {
              bind_directives.push_back(to_verilog_bind_directive(*it));
              it = items.erase(it);
            }
            else
              it++;
          }
        }

        item_it++;
      }
    }
  }

  return bind_directives;
}

void add_bind_directives(
  const std::vector<verilog_bind_directivet> &bind_directives,
  symbol_table_baset &symbol_table)
{
  if(bind_directives.empty())
    return;

  for(auto &bind_directive : bind_directives)
  {
    auto &target = bind_directive.target();

    if(target.id() == ID_verilog_identifier)
    {
      // Check that the target module exists.
      auto base_name = target.get(ID_base_name);
      auto source_identifier =
        id2string(verilog_module_symbol(base_name)) + "$source";

      if(symbol_table.lookup(source_identifier) == nullptr)
      {
        throw ebmc_errort{}.with_location(bind_directive.source_location())
          << "bind target `" << base_name << "' not found";
      }

      // Reject directives that bind a module to itself, which
      // would result in an unbounded recursion.
      if(bind_directive.instantiation().module_base_name() == base_name)
      {
        throw ebmc_errort{}.with_location(bind_directive.source_location())
          << "cannot bind module `" << base_name << "' to itself";
      }
    }
  }

  // Store the bind directives in the symbol table, to be
  // applied during elaboration.
  exprt value{ID_verilog_bind_directives};

  for(auto &bind_directive : bind_directives)
    value.add_to_operands(bind_directive);

  symbolt symbol{
    bind_directives_identifier(),
    typet{ID_verilog_bind_directives},
    ID_Verilog};
  symbol.base_name = "$bind_directives";
  symbol.value = std::move(value);

  auto add_result = symbol_table.add(symbol);
  CHECK_RETURN(!add_result);
}

void apply_bind_directives(
  verilog_module_sourcet &module_source,
  const irep_idt &module_base_name,
  const irep_idt &instance_identifier,
  const symbol_table_baset &symbol_table)
{
  auto symbol_ptr = symbol_table.lookup(bind_directives_identifier());

  if(symbol_ptr == nullptr)
    return; // no bind directives

  for(auto &op : symbol_ptr->value.operands())
  {
    auto &bind_directive = to_verilog_bind_directive(op);
    auto &target = bind_directive.target();

    bool matches;

    if(target.id() == ID_verilog_identifier)
    {
      // Module target: applies to all instances of the module.
      matches = target.get(ID_base_name) == module_base_name;
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

    if(target.id() == ID_hierarchical_identifier)
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
