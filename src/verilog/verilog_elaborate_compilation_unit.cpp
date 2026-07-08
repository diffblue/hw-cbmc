/*******************************************************************\

Module: Elaboration of Verilog Compilation Units

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "verilog_elaborate_compilation_unit.h"

#include <ebmc/ebmc_error.h>

#include "verilog_typecheck.h"

void verilog_elaborate_compilation_unit(
  const verilog_parse_treet &parse_tree,
  bool warn_implicit_nets,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  for(auto &item : parse_tree.items)
  {
    if(item.id() == ID_verilog_module || item.id() == ID_verilog_checker)
    {
      auto identifier =
        verilog_module_symbol(to_verilog_module_source(item).base_name());
      copy_module_source(item, identifier, symbol_table);
    }
    else if(item.id() == ID_verilog_interface)
    {
      auto identifier =
        verilog_module_symbol(to_verilog_interface(item).base_name());
      copy_module_source(item, identifier, symbol_table);
    }
    else if(item.id() == ID_verilog_package)
    {
      // IEEE 1800 2017 26.3 Referencing data in packages
      // "The compilation of a package shall precede the compilation of
      // scopes in which the package is imported."
      // We hence elaborate packages in their given order.

      messaget log{message_handler};

      // copy source
      auto identifier =
        verilog_package_identifier(to_verilog_module_source(item).base_name());
      copy_module_source(item, identifier, symbol_table);

      // type check the package
      log.status() << "Type-checking " << identifier << messaget::eom;

      if(verilog_typecheck(
           symbol_table,
           identifier,
           parse_tree.standard,
           warn_implicit_nets,
           message_handler))
      {
        log.error() << "CONVERSION ERROR" << messaget::eom;
        throw ebmc_errort{}.with_exit_code(2);
      }
    }
    else if(item.id() == ID_decl)
    {
      auto &decl = to_verilog_decl(item);
      auto decl_class = decl.get_class();

      // Out-of-body method definition for an interface (1800-2017 25.4.4)
      if(
        (decl_class == ID_function || decl_class == ID_task) &&
        !decl.declarators().empty() &&
        decl.declarators()[0].get_string(ID_verilog_scope_prefix) != "")
      {
        // Merge the out-of-body definition into the interface source.
        auto scope_prefix =
          decl.declarators()[0].get_string(ID_verilog_scope_prefix);
        // Remove trailing '.' to get interface name
        auto interface_name = scope_prefix.substr(0, scope_prefix.size() - 1);
        auto source_symbol_id = "Verilog::" + interface_name + "$source";

        auto *source_symbol = symbol_table.get_writeable(source_symbol_id);

        if(source_symbol == nullptr)
        {
          throw ebmc_errort{}.with_location(decl.source_location())
            << "interface `" << interface_name
            << "' not found for out-of-body method definition";
        }

        // Find the extern prototype in the interface items and replace it
        // with the full definition.
        auto &interface_source = static_cast<verilog_module_sourcet &>(
          source_symbol->type.add(ID_module_source));
        auto base_name = decl.declarators()[0].get(ID_base_name);

        bool found_extern = false;
        for(auto &iface_item : interface_source.module_items())
        {
          if(
            iface_item.id() == ID_decl &&
            to_verilog_decl(iface_item).get_class() == decl_class &&
            to_verilog_decl(iface_item).get_bool(ID_extern))
          {
            auto &extern_decl = to_verilog_decl(iface_item);
            if(
              !extern_decl.declarators().empty() &&
              extern_decl.declarators()[0].get(ID_base_name) == base_name)
            {
              // Replace the extern prototype with the full definition.
              // Keep ports from the out-of-body definition and add the body.
              iface_item = static_cast<const verilog_module_itemt &>(
                static_cast<const exprt &>(decl));
              // Remove the scope prefix and extern flag from the merged decl
              auto &merged = static_cast<verilog_declt &>(iface_item);
              merged.declarators()[0].remove(ID_verilog_scope_prefix);
              merged.remove(ID_extern);
              found_extern = true;
              break;
            }
          }
        }

        if(!found_extern)
        {
          throw ebmc_errort{}.with_location(decl.source_location())
            << "no matching extern prototype for `" << base_name
            << "' in interface `" << interface_name << "'";
        }
      }
      else
      {
        // compilation-unit scoped nets, variables, typedefs, functions,
        // tasks, parameters
        try
        {
          verilog_typecheckt verilog_typecheck(
            parse_tree.standard,
            warn_implicit_nets,
            symbol_table,
            message_handler);
          verilog_typecheck.typecheck_decl(to_verilog_decl(item));
        }
        catch(const typecheckt::errort &error)
        {
          if(!error.what().empty())
          {
            throw ebmc_errort{}.with_location(error.source_location())
              << error.what();
          }
          else
            throw ebmc_errort{};
        }
      }
    }
    else if(
      item.id() == ID_parameter_decl || item.id() == ID_local_parameter_decl)
    {
      // compilation-unit scoped parameters
      try
      {
        verilog_typecheckt verilog_typecheck(
          parse_tree.standard,
          warn_implicit_nets,
          symbol_table,
          message_handler);
        verilog_typecheck.typecheck_parameter_decl(
          static_cast<const verilog_module_itemt &>(item));
      }
      catch(const typecheckt::errort &error)
      {
        if(!error.what().empty())
        {
          throw ebmc_errort{}.with_location(error.source_location())
            << error.what();
        }
        else
          throw ebmc_errort{};
      }
    }
  }
}
