/*******************************************************************\

Module: Verilog Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_SYNTHESIS_CLASS_H
#define CPROVER_VERILOG_SYNTHESIS_CLASS_H

#include <util/mathematical_expr.h>
#include <util/mp_arith.h>
#include <util/options.h>
#include <util/std_expr.h>
#include <util/string_hash.h>

#include "sva_expr.h"
#include "verilog_expr.h"
#include "verilog_symbol_table.h"
#include "verilog_typecheck_base.h"

#include <map>
#include <set>
#include <unordered_set>

/*******************************************************************\

   Class: verilog_synthesist

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class verilog_synthesist:
  public verilog_typecheck_baset,
  public verilog_symbol_tablet
{
public:
  verilog_synthesist(
    verilog_standardt _standard,
    bool _ignore_initial,
    const namespacet &_ns,
    symbol_table_baset &_symbol_table,
    const irep_idt &_module,
    message_handlert &_message_handler)
    : verilog_typecheck_baset(_standard, _ns, _message_handler),
      verilog_symbol_tablet(_symbol_table),
      ignore_initial(_ignore_initial),
      value_map(NULL),
      module(_module),
      temporary_counter(0)
  {
  }

  virtual void typecheck();

  enum class symbol_statet
  {
    NONE,
    SYMBOL,
    CURRENT,
    FINAL
  };

  [[nodiscard]] exprt synth_expr(exprt expr, symbol_statet symbol_state);

protected:
  bool ignore_initial;

  [[nodiscard]] exprt synth_expr_rec(exprt expr, symbol_statet symbol_state);

  // For $ND(...)
  std::size_t nondet_count = 0;

  enum class event_guardt { NONE, CLOCK, COMBINATIONAL };
  
  inline std::string as_string(event_guardt g)
  {
    return g==event_guardt::CLOCK?"clocked":
           g==event_guardt::COMBINATIONAL?"combinational":
           "";
  }
  
  // list of vector-indices or array indices
  typedef std::list<mp_integer> membert;

  typedef std::list<membert> member_listt;
  
  static bool disjoint(const membert &a, const membert &b);
  
  // global assignment map
  class assignmentt
  {
  public:
    struct datat
    {
      exprt value;

      // array/bv indices that are already assigned to
      member_listt assigned_previous, assigned_current;
      
      datat():value(nil_exprt()) { }
      
      void move_assignments()
      {
        assigned_previous.splice(
          assigned_previous.end(),
          assigned_current);
      }
      
    } init, next;

    // only relevant for 'next'
    event_guardt type;
    bool is_cycle_local = false;

    assignmentt():type(event_guardt::NONE)
    {
    }
  };
   
  typedef std::map<irep_idt, assignmentt> assignmentst;
  assignmentst assignments;
  
  // for assumes
  typedef std::list<exprt> invarst;
  invarst invars;

  enum class constructt
  {
    INITIAL,
    ALWAYS,
    ALWAYS_COMB,
    ALWAYS_FF,
    ALWAYS_LATCH,
    OTHER
  };

  constructt construct;
  event_guardt event_guard;
 
  // current value map
  class value_mapt
  {
  public:
    class mapt
    {
    public:
      typedef std::map<irep_idt, exprt> symbol_mapt;
      symbol_mapt symbol_map;

      std::set<irep_idt> changed;
      
      void assign(const irep_idt &symbol, const exprt &rhs)
      {
        changed.insert(symbol);
        symbol_map[symbol]=rhs;
      }

    } current, final;

    void clear_changed()
    {
      current.changed.clear();
      final.changed.clear();
    }

    // current guard
    exprt::operandst guard;

    exprt guarded_expr(exprt) const;
  };

  // expressions
  [[nodiscard]] exprt synth_lhs_expr(exprt expr);
  [[nodiscard]] std::optional<mp_integer> synthesis_constant(const exprt &);

  exprt current_value(
    const value_mapt::mapt &map,
    const symbolt &,
    bool use_previous_assignments) const;

  exprt guarded_expr(exprt expr) const
  {
    PRECONDITION(value_map != NULL);
    return value_map->guarded_expr(expr);
  }

  inline exprt current_value(const symbolt &symbol) const
  {
    PRECONDITION(value_map != NULL);
    return current_value(value_map->current, symbol, false);
  }

  inline exprt final_value(const symbolt &symbol) const
  {
    PRECONDITION(value_map != NULL);
    return current_value(value_map->final, symbol, true);
  }

  value_mapt *value_map;
   
  void merge(
    const exprt &guard,
    const value_mapt::mapt &true_map,
    const value_mapt::mapt &false_map,
    bool use_previous_assignments,
    value_mapt::mapt &dest);
                                             
  const irep_idt &module;

  typedef std::unordered_set<irep_idt, irep_id_hash> local_symbolst;
  local_symbolst local_symbols, new_wires;

  void assignment_rec(const exprt &lhs, const exprt &rhs, bool blocking);

  void assignment_rec(
    const exprt &lhs,
    exprt &rhs,
    exprt &new_value);

  const symbolt &assignment_symbol(const exprt &lhs);

  void assignment_member_rec(
    const exprt &lhs,
    membert &member,
    assignmentt::datat &data);

  void add_assignment_member(
    const exprt &lhs,
    const membert &member,
    assignmentt::datat &data);

  static void set_default_sequence_semantics(exprt &, sva_sequence_semanticst);

  // module items
  virtual void convert_module_items(symbolt &);
  void synth_module_item(const verilog_module_itemt &, transt &);
  void synth_always_base(const verilog_always_baset &);
  void synth_assertion_item(const verilog_assertion_itemt &);
  void synth_initial(const verilog_initialt &);
  void
  synth_assert_assume_cover(const verilog_assert_assume_cover_module_itemt &);
  void synth_assume(const verilog_assert_assume_cover_module_itemt &);
  void synth_continuous_assign(const verilog_continuous_assignt &);
  void synth_force_rec(exprt &lhs, exprt &rhs, transt &);
  void synth_module_instance(const verilog_instt &, transt &);
  void synth_module_instance_builtin(const verilog_inst_builtint &, transt &);

  // statements
  void synth_statement(const verilog_statementt &);
  void synth_decl(const verilog_declt &);
  void synth_block(const verilog_blockt &);
  void synth_case(const verilog_statementt &);
  void synth_if(const verilog_ift &);
  void synth_event_guard(const verilog_event_guardt &);
  void synth_delay(const verilog_delayt &);
  void synth_for(const verilog_fort &);
  void synth_force(const verilog_forcet &);
  void synth_force_rec(const exprt &lhs, const exprt &rhs);
  void synth_forever(const verilog_forevert &);
  void synth_while(const verilog_whilet &);
  void synth_repeat(const verilog_repeatt &);
  void synth_function_call_or_task_enable(const verilog_function_callt &);
  void synth_assign(const verilog_assignt &);
  void
  synth_assert_assume_cover(const verilog_assert_assume_cover_statementt &);
  void synth_assume(const verilog_assume_statementt &);
  void synth_prepostincdec(const verilog_statementt &);
  void synth_assignments(transt &);

  exprt make_supply_value(const irep_idt &decl_class, const typet &);

  void post_process_initial(exprt &constraints);
  void post_process_wire(const irep_idt &identifier, exprt &expr);
  
  exprt case_comparison(const exprt &case_operand, const exprt &pattern);
  
  typedef enum { CURRENT, NEXT } curr_or_nextt;

  exprt symbol_expr(const symbolt &, curr_or_nextt curr_or_next) const;

  void extract_expr(exprt &dest, unsigned bit);

  void synth_assignments(
    const symbolt &symbol,
    curr_or_nextt curr_or_next,
    exprt &new_value,
    exprt &constraints);

  exprt synth_case_values(
    const exprt &values,
    const exprt &case_operand);

  void expand_module_instance(
    const symbolt &module_symbol,
    const verilog_instt::instancet &,
    transt &trans);

  void expand_hierarchical_identifier(
    class hierarchical_identifier_exprt &expr,
    symbol_statet symbol_state);

  exprt
  expand_function_call(const class function_call_exprt &call, symbol_statet);

  typedef std::map<irep_idt, exprt> replace_mapt;

  void instantiate_ports(
    const irep_idt &instance,
    const exprt &inst,
    const symbolt &,
    const replace_mapt &,
    transt &);

  bool replace_symbols(const replace_mapt &what, exprt &dest);
  void replace_symbols(const irep_idt &target, exprt &dest);

  void instantiate_port(
    bool is_output,
    const symbol_exprt &port,
    const exprt &value,
    const replace_mapt &,
    const source_locationt &,
    transt &);

  void replace_by_wire(exprt &expr, const symbolt &base);

  // Mark the local variables of a function or task
  // as cycle local.
  void function_locality(const symbolt &);

  unsigned temporary_counter;
};

#endif
