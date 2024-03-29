/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_MODULE_H
#define CPROVER_VERILOG_MODULE_H

#include <string>

#include <util/expr.h>

struct verilog_modulet
{
  irep_idt name;
  exprt parameter_port_list;
  exprt ports;
  exprt module_items;
  source_locationt location;
  
  irept to_irep() const
  {
    irept irep;
    irep.set(ID_name, name);
    irep.add(ID_parameter_port_list) = parameter_port_list;
    irep.add(ID_ports)=ports;
    irep.add(ID_module_items) = module_items;
    return irep;
  }
  
  void swap(verilog_modulet &m)
  {
    m.name.swap(name);
    m.ports.swap(ports);
    m.module_items.swap(module_items);
    m.location.swap(location);
  }
  
  void show(std::ostream &out) const;

  // The identifiers of the submodules
  // (not: the identifiers of the instances)
  std::vector<irep_idt> submodules() const;

private:
  static void
  submodules_rec(const exprt &module_item, std::vector<irep_idt> &dest);
};

#endif
