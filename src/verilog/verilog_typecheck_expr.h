/*******************************************************************\

Module: Verilog Expression Type Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_TYPECHEK_EXPR_H
#define CPROVER_VERILOG_TYPECHEK_EXPR_H

#include <cassert>

#include <util/mp_arith.h>
#include <util/namespace.h>
#include <util/std_expr.h>

#include "verilog_typecheck_base.h"

class verilog_typecheck_exprt:public verilog_typecheck_baset
{
public:
  verilog_typecheck_exprt(
    const namespacet &_ns,
    message_handlert &_message_handler):
    verilog_typecheck_baset(_ns, _message_handler),
    nondet_count(0)
  { }

  verilog_typecheck_exprt(
    const namespacet &_ns,
    const std::string &_module_identifier,
    message_handlert &_message_handler):
    verilog_typecheck_baset(_ns, _message_handler),
    module_identifier(_module_identifier),
    nondet_count(0)
  { }

  virtual void convert_expr(exprt &expr);
  virtual void convert_const_expression(const exprt &expr, mp_integer &value);

protected:
  irep_idt module_identifier;
  irep_idt function_or_task_name;
  unsigned nondet_count;
  
  void make_boolean(exprt &expr);

  void propagate_type(exprt &expr, const typet &type);

  virtual void convert_type(const irept &src, typet &dest);

  virtual void convert_range(
    const exprt &range,
    mp_integer &msb,
    mp_integer &lsb);
    
  virtual void genvar_value(
    const irep_idt &identifier,
    mp_integer &value)
  {
    assert(false);
  }
    
  virtual bool implicit_wire(
    const irep_idt &identifier,
    const symbolt *&symbol)
  {
    return true;
  }
   
  virtual void typecheck()
  {
  }

  typet max_type(const typet &t1, const typet &t2);

private:
  bool is_const_expression(const exprt &expr, mp_integer &value);
  void convert_constant(constant_exprt &expr);
  void convert_symbol(exprt &expr);
  void convert_hierarchical_identifier(class hierarchical_identifier_exprt &expr);
  void convert_nullary_expr(exprt &expr);
  void convert_unary_expr  (exprt &expr);
  void convert_binary_expr (exprt &expr);
  void convert_trinary_expr(exprt &expr);
  void convert_expr_function_call(class function_call_exprt &expr);
  void convert_system_function(const irep_idt &identifier,
                               class function_call_exprt &expr);
  void convert_constraint_select_one(exprt &expr);
  void typecast(exprt &expr, const typet &type);
  void tc_binary_expr(exprt &expr);
  void tc_binary_expr(const exprt &expr, exprt &op0, exprt &op1);
  void no_bool(exprt &expr);
};

bool verilog_typecheck(
  exprt &expr,
  const std::string &module_identifier,
  message_handlert &message_handler,
  const namespacet &ns);

#endif
