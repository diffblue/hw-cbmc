/*******************************************************************\

Module: Verilog Type Checker Base

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_TYPECHEK_BASE_H
#define CPROVER_VERILOG_TYPECHEK_BASE_H

#include <util/mp_arith.h>
#include <util/namespace.h>
#include <util/typecheck.h>

#include "verilog_standard.h"

irep_idt verilog_module_symbol(const irep_idt &base_name);
irep_idt verilog_module_name(const irep_idt &identifier);
irep_idt strip_verilog_prefix(const irep_idt &identifier);

class array_typet;

class verilog_typecheck_baset:public typecheckt
{
public:
  verilog_typecheck_baset(
    verilog_standardt _standard,
    const namespacet &_ns,
    message_handlert &_message_handler)
    : typecheckt(_message_handler),
      standard(_standard),
      ns(_ns),
      mode(ID_Verilog)
  { }

  // overloaded to use verilog syntax
  
  std::string to_string(const typet &type);
  std::string to_string(const exprt &expr);

protected:
  verilog_standardt standard;
  const namespacet &ns;
  const irep_idt mode;

  mp_integer get_width(const exprt &expr)
  {
    return get_width(expr.type());
  }
  mp_integer get_width(const typet &type);
  mp_integer array_size(const array_typet &);
  mp_integer array_offset(const array_typet &);
  typet index_type(const array_typet &);
};

#endif
