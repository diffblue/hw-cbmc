/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_TYPECHECK_H
#define CPROVER_VERILOG_TYPECHECK_H

#include <util/mp_arith.h>
#include <util/replace_expr.h>
#include <util/symbol_table_base.h>
#include <util/typecheck.h>

#include "verilog_expr.h"
#include "verilog_parse_tree.h"
#include "verilog_symbol_table.h"
#include "verilog_typecheck_expr.h"

bool verilog_typecheck(
  const verilog_parse_treet &parse_tree,
  symbol_table_baset &,
  const std::string &module,
  message_handlert &message_handler);

bool verilog_typecheck(
  symbol_table_baset &,
  const verilog_modulet &verilog_module,
  message_handlert &message_handler);

bool verilog_typecheck(
  symbol_table_baset &,
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
    symbol_table_baset &_symbol_table,
    message_handlert &_message_handler)
    : verilog_typecheck_exprt(ns, _message_handler),
      verilog_symbol_tablet(_symbol_table),
      ns(_symbol_table),
      module_symbol(_module_symbol),
      assertion_counter(0)
  {}

  void typecheck() override;

protected:
  const namespacet ns;
  symbolt &module_symbol;

  // Parameters.
  // defparam assignments. Map from module instance names
  // to a map from parameter names to values.
  using defparamst = std::map<irep_idt, std::map<irep_idt, exprt>>;
  defparamst defparams;

  void elaborate_constants();
  void elaborate_parameter(irep_idt) override;

  // instances
  irep_idt parameterize_module(
    const source_locationt &location,
    const irep_idt &module_identifier,
    const exprt::operandst &parameter_assignment,
    const std::map<irep_idt, exprt> &defparams);

  std::vector<verilog_parameter_declt::declaratort>
  get_parameter_declarators(const verilog_module_sourcet &);

  std::list<exprt> get_parameter_values(
    const verilog_module_sourcet &,
    const exprt::operandst &parameter_assignment,
    const std::map<irep_idt, exprt> &defparams);

  void set_parameter_values(
    verilog_module_sourcet &,
    const std::list<exprt> &parameter_values);

  // interfaces
  void module_interface(const verilog_module_sourcet &);
  void check_module_ports(const verilog_module_sourcet &);
  void interface_module_decl(const class verilog_declt &);
  void interface_function_or_task_decl(const class verilog_declt &);
  void interface_inst(const class verilog_module_itemt &);
  void interface_inst(const class verilog_module_itemt &, const exprt &op);
  void interface_module_item(const class verilog_module_itemt &);
  void interface_block(const class verilog_blockt &);
  void interface_generate_block(const class verilog_generate_blockt &);
  void interface_statement(const class verilog_statementt &);
  void interface_function_or_task(const class verilog_declt &);

  array_typet array_type(
    const irept &src,
    const typet &element_type);

  // type checking
  
  typedef enum { A_CONTINUOUS, A_BLOCKING, A_NON_BLOCKING } vassignt;

  // statements
  void convert_statement(class verilog_statementt &);
  void convert_function_call_or_task_enable(class verilog_function_callt &);
  void convert_block(class verilog_blockt &);
  void convert_case(class verilog_case_baset &);
  void convert_if(class verilog_ift &);
  void convert_event_guard(class verilog_event_guardt &);
  void convert_delay(class verilog_delayt &);
  void convert_for(class verilog_fort &);
  void convert_force(class verilog_forcet &);
  void convert_forever(class verilog_forevert &);
  void convert_while(class verilog_whilet &);
  void convert_repeat(class verilog_repeatt &);
  void convert_assign(class verilog_assignt &, bool blocking);
  void convert_procedural_continuous_assign(
    class verilog_procedural_continuous_assignt &);
  void convert_prepostincdec(class verilog_statementt &);
  
  // module items
  void convert_decl(class verilog_declt &);
  void convert_function_or_task(class verilog_declt &);
  void convert_inst(class verilog_instt &);
  void convert_inst_builtin(class verilog_inst_builtint &);
  void convert_always(class verilog_alwayst &);
  void convert_initial(class verilog_initialt &);
  void convert_continuous_assign(class verilog_continuous_assignt &);
  void convert_assert(exprt &statement);
  void convert_assume(exprt &statement);
  void check_lhs(const exprt &lhs, vassignt vassign);
  void convert_assignments(exprt &trans);
  void convert_module_item(class verilog_module_itemt &);
  void convert_parameter_override(const class verilog_parameter_overridet &);

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

  // to be overridden
  virtual void convert_statements(verilog_module_exprt &);

  // to be overridden
  bool implicit_wire(const irep_idt &identifier,
                     const symbolt *&symbol) override;

  using module_itemst = std::vector<verilog_module_itemt>;

  // generate constructs
  verilog_module_exprt
  elaborate_generate_constructs(const verilog_module_sourcet &);
  void elaborate_generate_assign(const exprt &statement, module_itemst &dest);
  void elaborate_generate_block(
    const verilog_generate_blockt &,
    module_itemst &dest);
  void elaborate_generate_decl(const verilog_declt &, module_itemst &dest);
  void elaborate_generate_inst(const verilog_instt &, module_itemst &dest);
  void elaborate_generate_item(const exprt &statement, module_itemst &dest);
  void elaborate_generate_if(const exprt &statement, module_itemst &dest);
  void elaborate_generate_case(const exprt &statement, module_itemst &dest);
  void elaborate_generate_for(const exprt &statement, module_itemst &dest);
  exprt generate_for_loop_index(const exprt &initialization_statement) const;

  // generate state
  typedef std::map<irep_idt, mp_integer> genvarst;
  genvarst genvars;

  // to be overridden
  void genvar_value(const irep_idt &identifier, mp_integer &value) override {
    genvarst::const_iterator it=genvars.find(identifier);
    if(it==genvars.end())
      value=-1;
    else
      value=it->second;
  }

  // interpreter state
  typedef std::map<irep_idt, exprt> varst;
  varst vars;

  exprt var_value(const irep_idt &identifier) override {
    varst::const_iterator it=vars.find(identifier);
    if(it==vars.end())
      return nil_exprt();
    else
      return it->second;
  }

  // constant function calls, 13.4.3 IEEE 1800-2017
  exprt
  elaborate_constant_function_call(const class function_call_exprt &) override;

  void verilog_interpreter(const class verilog_statementt &);
  
  // counter for assertions
  unsigned assertion_counter;
};

#endif
