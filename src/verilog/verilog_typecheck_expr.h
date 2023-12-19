/*******************************************************************\

Module: Verilog Expression Type Checker

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_TYPECHEK_EXPR_H
#define CPROVER_VERILOG_TYPECHEK_EXPR_H

#include <util/bitvector_expr.h>
#include <util/mp_arith.h>
#include <util/namespace.h>
#include <util/std_expr.h>

#include "verilog_typecheck_base.h"

#include <cassert>
#include <stack>

class function_call_exprt;

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

  virtual void convert_expr(exprt &expr)
  {
    expr = convert_expr_rec(std::move(expr));
  }

  mp_integer convert_integer_constant_expression(exprt);

  exprt elaborate_constant_system_function_call(function_call_exprt);

protected:
  irep_idt module_identifier;
  irep_idt function_or_task_name;
  unsigned nondet_count;

  // module_identifier.function.block.base_name
  // including the Verilog:: prefix.
  irep_idt hierarchical_identifier(irep_idt base_name) const;

  void make_boolean(exprt &expr);

  void propagate_type(exprt &expr, const typet &type);

  typet convert_type(const typet &);
  typet convert_enum(const class verilog_enum_typet &);

  void convert_range(
    const exprt &range,
    mp_integer &msb,
    mp_integer &lsb);

  // to be overridden
  virtual mp_integer genvar_value(const irep_idt &identifier)
  {
    PRECONDITION(false);
  }

  virtual void elaborate_rec(irep_idt)
  {
    PRECONDITION(false);
  }

  // to be overridden
  virtual exprt var_value(const irep_idt &identifier)
  {
    PRECONDITION(false);
  }

  virtual bool implicit_wire(const irep_idt &identifier,
                             const symbolt *&symbol) {
    return true;
  }
   
  void typecheck() override
  {
  }

  typet max_type(const typet &t1, const typet &t2);

  // named blocks
  typedef std::vector<std::string> named_blockst;
  named_blockst named_blocks;
  void enter_named_block(const irep_idt &);

  // elaboration (expansion and folding) of constant expressions and functions
  bool is_constant_expression(const exprt &, mp_integer &value);
  exprt elaborate_constant_expression(exprt);

  // To be overridden, requires a Verilog interpreter.
  virtual exprt elaborate_constant_function_call(const function_call_exprt &)
  {
    assert(false);
  }

private:
  [[nodiscard]] exprt convert_expr_rec(exprt expr);
  [[nodiscard]] exprt convert_constant(constant_exprt);
  [[nodiscard]] exprt convert_symbol(symbol_exprt);
  [[nodiscard]] exprt
    convert_hierarchical_identifier(class hierarchical_identifier_exprt);
  [[nodiscard]] exprt convert_nullary_expr(nullary_exprt);
  [[nodiscard]] exprt convert_unary_expr(unary_exprt);
  [[nodiscard]] exprt convert_binary_expr(binary_exprt);
  [[nodiscard]] exprt convert_trinary_expr(ternary_exprt);
  [[nodiscard]] exprt convert_expr_function_call(function_call_exprt);
  [[nodiscard]] exprt
  convert_system_function(const irep_idt &identifier, function_call_exprt);
  [[nodiscard]] exprt convert_constraint_select_one(exprt);
  [[nodiscard]] exprt convert_extractbit_expr(extractbit_exprt);
  [[nodiscard]] exprt convert_replication_expr(replication_exprt);
  [[nodiscard]] exprt convert_shl_expr(shl_exprt);
  void typecast(exprt &, const typet &type);
  void tc_binary_expr(exprt &);
  void tc_binary_expr(const exprt &expr, exprt &op0, exprt &op1);
  void no_bool_ops(exprt &);

  exprt bits(const exprt &);
  std::optional<mp_integer> bits_rec(const typet &) const;
};

bool verilog_typecheck(
  exprt &,
  const std::string &module_identifier,
  message_handlert &,
  const namespacet &);

#endif
