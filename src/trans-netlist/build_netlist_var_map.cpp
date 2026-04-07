/*******************************************************************\

Module: var_map for Netlist

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "build_netlist_var_map.h"

#include <util/namespace.h>

#include <solvers/flattening/boolbv_width.h>

var_mapt
build_netlist_var_map(symbol_table_baset &symbol_table, const irep_idt &module)
{
  const namespacet ns{symbol_table};
  boolbv_widtht boolbv_width(ns);
  var_mapt var_map;

  auto update_dest_var_map = [&var_map, &boolbv_width](const symbolt &symbol)
  {
    var_mapt::vart::vartypet vartype;

    if(symbol.is_property)
      return; // ignore properties
    else if(
      symbol.type.id() == ID_verilog_sva_named_sequence ||
      symbol.type.id() == ID_verilog_sva_named_property)
    {
      return; // ignore sequence/property declarations
    }
    else if(
      symbol.type.id() == ID_natural || symbol.type.id() == ID_integer ||
      symbol.type.id() == ID_verilog_genvar)
    {
      return; // ignore
    }
    else if(symbol.type.id() == ID_smv_set)
    {
      return; // ignore
    }
    else if(
      symbol.type.id() == ID_module || symbol.type.id() == ID_module_instance ||
      symbol.type.id() == ID_primitive_module_instance ||
      symbol.type.id() == ID_smv_module_instance)
    {
      return; // ignore modules
    }
    else if(symbol.type.id() == ID_named_block)
    {
      return; // ignore Verilog named blocks
    }
    else if(symbol.is_type)
      return; // ignore types
    else if(symbol.is_input)
      vartype = var_mapt::vart::vartypet::INPUT;
    else if(symbol.is_state_var)
      vartype = var_mapt::vart::vartypet::LATCH;
    else
      vartype = var_mapt::vart::vartypet::WIRE;

    std::size_t size = boolbv_width(symbol.type);

    if(size == 0)
      return;

    var_mapt::vart &var = var_map.map[symbol.name];
    var.vartype = vartype;
    var.type = symbol.type;
    var.mode = symbol.mode;
    var.bits.resize(size);
  };

  for(const auto &symbol_it : symbol_table.symbols)
    if(symbol_it.second.module == module)
      update_dest_var_map(symbol_it.second);

  return var_map;
}
