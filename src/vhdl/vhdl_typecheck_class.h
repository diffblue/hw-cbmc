/*******************************************************************\

Module: VHDL Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VHDL_TYPECHECK_CLASS_H
#define CPROVER_VHDL_TYPECHECK_CLASS_H

#include <util/typecheck.h>
#include <util/namespace.h>

/*******************************************************************\

   Class: vhdl_typecheckt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class vhdl_typecheckt:public typecheckt
{
public:
  vhdl_typecheckt(
    const vhdl_parse_treet &_parse_tree,
    const irep_idt &_module_name,
    symbol_tablet &_symbol_table,
    message_handlert &_message_handler):
    typecheckt(_message_handler),
    ns(_symbol_table),
    parse_tree(_parse_tree),
    module_name(_module_name),
    symbol_table(_symbol_table)
  {
  }

  virtual void typecheck();

protected:
  const namespacet ns;
  const vhdl_parse_treet &parse_tree;
  const irep_idt &module_name;
  symbol_tablet &symbol_table;

  void typecheck_architecture(
    const vhdl_parse_treet::itemt &);
  
  void typecheck_architecture_entity(irept &);
  void typecheck_architecture_decl(irept &);
  void typecheck_architecture_body(irept &);
  
  #if 0
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
  void interface_module_decl(const class vhdl_declt &decl);
  void interface_function_or_task_decl(const class vhdl_declt &decl);
  void interface_parameter(const exprt &expr);
  void interface_parameter_decl(const exprt &statement);
  void interface_inst(const class vhdl_module_itemt &statement);
  void interface_inst(const class vhdl_module_itemt &statement, const exprt &op);
  void interface_module_item(const class vhdl_module_itemt &module_item);
  void interface_block(const class vhdl_blockt &statement);
  void interface_statement(const class vhdl_statementt &statement);
  void interface_function_or_task(const class vhdl_declt &decl);

  array_typet array_type(
    const irept &src,
    const typet &element_type);

  // type checking
  
  typedef enum { A_CONTINUOUS, A_BLOCKING, A_NON_BLOCKING } vassignt;

  // statements
  void convert_statement(class vhdl_statementt &statement);
  void convert_function_call_or_task_enable(class vhdl_function_callt &statement);
  void convert_block(class vhdl_blockt &statement);
  void convert_case(class vhdl_case_baset &statement);
  void convert_if(class vhdl_ift &statement);
  void convert_event_guard(class vhdl_event_guardt &statement);
  void convert_delay(class vhdl_delayt &statement);
  void convert_for(class vhdl_fort &statement);
  void convert_forever(class vhdl_forevert &statement);
  void convert_while(class vhdl_whilet &statement);
  void convert_repeat(class vhdl_repeatt &statement);
  void convert_assign(class vhdl_assignt &statement, bool blocking);
  void convert_procedural_continuous_assign(
    class vhdl_procedural_continuous_assignt &statement);
  void convert_prepostincdec(class vhdl_statementt &statement);
  
  // module items
  void convert_decl(class vhdl_declt &module_item);
  void convert_function_or_task(class vhdl_declt &decl);
  void convert_inst(class vhdl_instt &module_item);
  void convert_inst_builtin(class vhdl_inst_builtint &module_item);
  void convert_always(class vhdl_alwayst &module_item);
  void convert_initial(class vhdl_initialt &module_item);
  void convert_continuous_assign(class vhdl_continuous_assignt &module_item);
  void convert_assert(exprt &statement);
  void convert_assume(exprt &statement);
  void check_lhs(const exprt &lhs, vassignt vassign);
  void convert_assignments(exprt &trans);
  void convert_module_item(class vhdl_module_itemt &module_item);

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
  #endif
};

#endif
