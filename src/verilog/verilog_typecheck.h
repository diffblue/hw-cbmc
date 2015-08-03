/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_TYPECHECK_H
#define CPROVER_VERILOG_TYPECHECK_H

#include <util/hash_cont.h>
#include <util/symbol_table.h>
#include <util/typecheck.h>
#include <util/mp_arith.h>
#include <util/replace_expr.h>

#include "verilog_typecheck_expr.h"
#include "verilog_parse_tree.h"
#include "verilog_symbol_table.h"

bool verilog_typecheck(
  const verilog_parse_treet &parse_tree,
  symbol_tablet &symbol_table,
  const std::string &module,
  message_handlert &message_handler);

bool verilog_typecheck(
  symbol_tablet &symbol_table,
  const verilog_modulet &verilog_module,
  message_handlert &message_handler);

bool verilog_typecheck(
  symbol_tablet &symbol_table,
  const std::string &module_identifier,
  const exprt::operandst &parameters,
  message_handlert &message_handler);

/*******************************************************************\

   Class: verilog_typecheckt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class verilog_typecheckt:
  public verilog_typecheck_exprt,
  public verilog_symbol_tablet
{
public:
  verilog_typecheckt(
    symbolt &_module_symbol,
    symbol_tablet &_symbol_table,
    message_handlert &_message_handler):
    verilog_typecheck_exprt(ns, _message_handler),
    verilog_symbol_tablet(_symbol_table),
    ns(_symbol_table),
    module_symbol(_module_symbol),
    assertion_counter(0)
  {}

  virtual void typecheck();

protected:
  const namespacet ns;
  symbolt &module_symbol;

  // instances
  irep_idt parameterize_module(
    const source_locationt &location,
    const irep_idt &module_identifier,
    const exprt::operandst &parameter_assignment);

  void get_parameter_values(
    const irept &module_source,
    const exprt::operandst &parameter_assignment,
    expr_listt &parameter_values);

  void set_parameter_values(
    irept &module_source,
    const expr_listt &parameter_values);

  // interfaces
  void module_interface();
  void interface_ports(irept::subt &ports);
  void interface_module_decl(const class verilog_declt &decl);
  void interface_function_or_task_decl(const class verilog_declt &decl);
  void interface_parameter(const exprt &expr);
  void interface_parameter_decl(const exprt &statement);
  void interface_inst(const class verilog_module_itemt &statement);
  void interface_inst(const class verilog_module_itemt &statement, const exprt &op);
  void interface_module_item(const class verilog_module_itemt &module_item);
  void interface_block(const class verilog_blockt &statement);
  void interface_statement(const class verilog_statementt &statement);
  void interface_function_or_task(const class verilog_declt &decl);

  void array_type(
    const irept &src,
    const typet &element_type,
    typet &dest);

  // type checking
  
  typedef enum { A_CONTINUOUS, A_BLOCKING, A_NON_BLOCKING } vassignt;

  // statements
  void convert_statement(class verilog_statementt &statement);
  void convert_function_call_or_task_enable(class verilog_function_callt &statement);
  void convert_block(class verilog_blockt &statement);
  void convert_case(class verilog_case_baset &statement);
  void convert_if(class verilog_ift &statement);
  void convert_event_guard(class verilog_event_guardt &statement);
  void convert_delay(class verilog_delayt &statement);
  void convert_for(class verilog_fort &statement);
  void convert_forever(class verilog_forevert &statement);
  void convert_while(class verilog_whilet &statement);
  void convert_repeat(class verilog_repeatt &statement);
  void convert_assign(class verilog_assignt &statement, bool blocking);
  void convert_procedural_continuous_assign(
    class verilog_procedural_continuous_assignt &statement);
  void convert_prepostincdec(class verilog_statementt &statement);
  
  // module items
  void convert_decl(class verilog_declt &module_item);
  void convert_function_or_task(class verilog_declt &decl);
  void convert_inst(class verilog_instt &module_item);
  void convert_inst_builtin(class verilog_inst_builtint &module_item);
  void convert_always(class verilog_alwayst &module_item);
  void convert_initial(class verilog_initialt &module_item);
  void convert_continuous_assign(class verilog_continuous_assignt &module_item);
  void convert_assert(exprt &statement);
  void convert_assume(exprt &statement);
  void check_lhs(const exprt &lhs, vassignt vassign);
  void convert_assignments(exprt &trans);
  void convert_module_item(class verilog_module_itemt &module_item);

  void integer_expr(exprt &expr);

  void convert_case_values(
    exprt &values,
    const exprt &case_operand);

  void instantiate_port_connections(
    const std::string &instance,
    const exprt &inst,
    const symbolt &symbol,
    exprt &trans);

  void typecheck_port_connections(
    exprt &inst,
    const symbolt &symbol);

  void typecheck_builtin_port_connections(exprt &inst);

  void typecheck_port_connection(
    exprt &op,
    const exprt &port);

  bool replace_symbols(const replace_mapt &what, exprt &dest);
  void replace_symbols(const std::string &target, exprt &dest);

  virtual void convert_statements();

  virtual bool implicit_wire(
    const irep_idt &identifier,
    const symbolt *&symbol);
    
  // override parameter values
  typedef std::map<std::string, exprt> overridest;
  overridest overrides;
  
  // generate constructs
  void elaborate_generate_assign(const exprt &statement, exprt::operandst &dest);
  void elaborate_generate_block(const exprt &statement, exprt::operandst &dest);
  void elaborate_generate_item(const exprt &statement, exprt::operandst &dest);
  void elaborate_generate_if(const exprt &statement, exprt::operandst &dest);
  void elaborate_generate_case(const exprt &statement, exprt::operandst &dest);
  void elaborate_generate_for(const exprt &statement, exprt::operandst &dest);

  // generate state
  typedef std::map<irep_idt, mp_integer> genvarst;
  genvarst genvars;

  virtual void genvar_value(
    const irep_idt &identifier,
    mp_integer &value)
  {
    genvarst::const_iterator it=genvars.find(identifier);
    if(it==genvars.end())
      value=-1;
    else
      value=it->second;
  }
  
  // counter for assertions
  unsigned assertion_counter;
};

#endif
