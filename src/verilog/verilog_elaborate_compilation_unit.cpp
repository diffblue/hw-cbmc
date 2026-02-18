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
      // compilation-unit scoped nets, variables, typedefs, functions,
      // tasks, parameters
      verilog_typecheckt verilog_typecheck(
        parse_tree.standard, warn_implicit_nets, symbol_table, message_handler);
      verilog_typecheck.typecheck_decl(to_verilog_decl(item));
    }
  }
}
