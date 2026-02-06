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
  symbol_table_baset &,
  const irep_idt &module_identifier,
  verilog_standardt,
  bool warn_implicit_nets,
  message_handlert &message_handler);

/// copies the source of the given Verilog module or package
/// into the symbol table
symbolt &copy_module_source(
  const verilog_parse_treet::itemt module_item,
  const irep_idt &module_identifier,
  symbol_table_baset &);

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
    verilog_standardt _standard,
    bool warn_implicit_nets,
    symbolt &_module_symbol,
    symbol_table_baset &_symbol_table,
    message_handlert &_message_handler)
    : verilog_typecheck_exprt(
        _standard,
        warn_implicit_nets,
        ns,
        _message_handler),
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

  // Elaboration
  using module_itemst = verilog_module_sourcet::module_itemst;

  verilog_module_exprt elaborate(const verilog_module_sourcet &);
  module_itemst elaborate_level(const module_itemst &);
  void elaborate_symbol_rec(irep_idt) override;
  void add_symbol(symbolt);
  void collect_symbols(const typet &);
  void collect_symbols(const verilog_module_sourcet &);
  void collect_symbols(const verilog_module_itemt &);
  void collect_symbols(const verilog_declt &);
  void collect_symbols(const verilog_function_or_task_declt &);
  void collect_symbols(const verilog_lett &);
  void collect_symbols(const verilog_statementt &);
  void collect_symbols(const verilog_property_declarationt &);
  void collect_symbols(const verilog_sequence_declarationt &);
  void
  collect_symbols(const typet &, const verilog_parameter_declt::declaratort &);
  void collect_port_symbols(const verilog_declt &);
  std::vector<irep_idt> symbols_added;
  std::set<irep_idt> let_symbols;

  // instances
  void elaborate_inst(const verilog_inst_baset &);

  void
  elaborate_inst(const verilog_inst_baset &, const verilog_instt::instancet &);

  void elaborate_module_instances(const verilog_module_itemt &);

  irep_idt parameterize_module(
    const source_locationt &location,
    const irep_idt &module_identifier,
    const exprt::operandst &parameter_assignment,
    const std::map<irep_idt, exprt> &defparams);

  irep_idt parameterized_module_identifier(
    const irep_idt &module_identifier,
    const std::list<exprt> &parameter_values) const;

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
  void check_module_ports(const verilog_module_sourcet::port_listt &);
  void interface_module_item(const class verilog_module_itemt &);
  void interface_block(const class verilog_blockt &);
  void interface_generate_block(const class verilog_generate_blockt &);
  void interface_statement(const class verilog_statementt &);

  // type checking

  typedef enum
  {
    A_CONTINUOUS,
    A_BLOCKING,
    A_NON_BLOCKING,
    A_PROCEDURAL_CONTINUOUS
  } vassignt;

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
  void convert_return(class verilog_returnt &);
  void convert_assign(class verilog_assignt &, bool blocking);
  void convert_procedural_continuous_assign(
    class verilog_procedural_continuous_assignt &);
  void convert_prepostincdec(class verilog_statementt &);
  void convert_assert_assume_cover(verilog_assert_assume_cover_statementt &);
  void convert_assume(verilog_assume_statementt &);

  // module items
  void convert_decl(class verilog_declt &);
  void convert_function_or_task(class verilog_function_or_task_declt &);
  void convert_inst(class verilog_instt &);
  void convert_inst_builtin(class verilog_inst_builtint &);
  void convert_always_base(class verilog_always_baset &);
  void convert_initial(class verilog_initialt &);
  void convert_continuous_assign(class verilog_continuous_assignt &);
  void convert_assert_assume_cover(verilog_assert_assume_cover_module_itemt &);
  void check_lhs(const exprt &lhs, vassignt vassign);
  void convert_assignments(exprt &trans);
  void convert_module_item(class verilog_module_itemt &);
  void convert_parameter_override(const class verilog_parameter_overridet &);
  void convert_property_declaration(class verilog_property_declarationt &);
  void convert_sequence_declaration(class verilog_sequence_declarationt &);

  void integer_expr(exprt &expr);

  void convert_case_values(
    exprt &values,
    const exprt &case_operand);

  void instantiate_port_connections(
    const std::string &instance,
    const verilog_inst_baset::instancet &,
    const symbolt &symbol,
    exprt &trans);

  void typecheck_port_connections(
    verilog_inst_baset::instancet &,
    const symbolt &symbol);

  void typecheck_builtin_port_connections(verilog_inst_baset::instancet &);

  void typecheck_port_connection(exprt &op, const module_typet::portt &);

  bool replace_symbols(const replace_mapt &what, exprt &dest);
  void replace_symbols(const std::string &target, exprt &dest);

  // to be overridden
  virtual void convert_statements(verilog_module_exprt &);

  // to be overridden
  bool implicit_wire(
    const irep_idt &identifier,
    const symbolt *&,
    const typet &) override;

  // generate constructs
  void elaborate_generate_assign(
    const verilog_generate_assignt &,
    module_itemst &dest);
  void elaborate_generate_block(
    const verilog_generate_blockt &,
    module_itemst &dest);
  [[nodiscard]] module_itemst
  elaborate_generate_item(const verilog_module_itemt &);
  void
  elaborate_generate_item(const verilog_module_itemt &src, module_itemst &dest);
  void elaborate_generate_if(const verilog_generate_ift &, module_itemst &dest);
  void
  elaborate_generate_case(const verilog_generate_caset &, module_itemst &dest);
  void elaborate_generate_decl(const verilog_generate_declt &, module_itemst &);
  void
  elaborate_generate_for(const verilog_generate_fort &, module_itemst &dest);
  exprt
  generate_for_loop_index(const verilog_module_itemt &initialization) const;

  // generate state
  typedef std::map<irep_idt, mp_integer> genvarst;
  genvarst genvars;

  mp_integer genvar_value(const irep_idt &identifier) override
  {
    genvarst::const_iterator it=genvars.find(identifier);
    if(it==genvars.end())
      return -1;
    else
      return it->second;
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
