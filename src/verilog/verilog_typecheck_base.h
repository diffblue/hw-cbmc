/*******************************************************************\

Module: Verilog Type Checker Base

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_TYPECHEK_BASE_H
#define CPROVER_VERILOG_TYPECHEK_BASE_H

#include <util/symbol_table.h>
#include <util/typecheck.h>
#include <util/mp_arith.h>
#include <util/namespace_utils.h>

irep_idt verilog_module_symbol(const irep_idt &base_name);
irep_idt verilog_module_name(const irep_idt &identifier);

class verilog_typecheck_baset:public legacy_typecheckt,
                              public namespace_utilst
{
public:
  verilog_typecheck_baset(
    const namespacet &_ns,
    message_handlert &_message_handler):
    legacy_typecheckt(_message_handler),
    namespace_utilst(_ns),
    mode(ID_Verilog)
  { }

  // overloaded to use verilog syntax
  
  virtual std::string to_string(const typet &type);
  virtual std::string to_string(const exprt &expr);

protected:
  const irep_idt mode;
  
  void convert_type(const irept &src, typet &dest);
  virtual unsigned get_width(const exprt &expr) { return get_width(expr.type()); }
  virtual unsigned get_width(const typet &type);
  mp_integer array_size(const typet &type);
  mp_integer array_offset(const typet &type);
  typet index_type(const typet &array_type);
};

#endif
