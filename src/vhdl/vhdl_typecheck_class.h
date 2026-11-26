/*******************************************************************\

Module: VHDL Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VHDL_VHDL_TYPECHECK_CLASS_H
#define CPROVER_VHDL_VHDL_TYPECHECK_CLASS_H

#include <util/namespace.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table_base.h>
#include <util/typecheck.h>

#include "vhdl_expr.h"
#include "vhdl_parse_tree.h"
#include "vhdl_types.h"

#include <map>
#include <optional>
#include <set>
#include <vector>

/// Type checking of the architecture for one entity.
///
/// The result is a module symbol whose value has
/// * `ID_body`, the concurrent statements, type checked;
///
/// and symbols for the ports, signals and process variables of the
/// design. Constants are inlined, and enumeration literals are
/// turned into constants of the enumeration type.
///
/// The expressions have VHDL types (vhdl_types.h); the mapping to
/// CBMC types is done by vhdl_lowering, after synthesis. Statements
/// are turned into codet. Names are resolved into symbol expressions,
/// indexed names into index expressions, slices into vhdl_slice
/// expressions with static bounds, and the clock edge expressions
/// clk'event and rising_edge(clk) into vhdl_event and vhdl_rising_edge.
class vhdl_typecheckt : public typecheckt
{
public:
  vhdl_typecheckt(
    const vhdl_parse_treet &_parse_tree,
    irep_idt _module_name,
    symbol_table_baset &_symbol_table,
    message_handlert &_message_handler)
    : typecheckt(_message_handler),
      ns(_symbol_table),
      parse_tree(_parse_tree),
      module_name(_module_name),
      symbol_table(_symbol_table)
  {
  }

  void typecheck() override;

protected:
  const namespacet ns;
  const vhdl_parse_treet &parse_tree;
  const irep_idt module_name;
  symbolt *module_symbol = nullptr;
  symbol_table_baset &symbol_table;

  // design units
  void typecheck_architecture(const vhdl_parse_treet::itemt &);
  void typecheck_entity(const vhdl_parse_treet::itemt &);
  void typecheck_package(const vhdl_parse_treet::itemt &);

  // declarations
  void typecheck_interface_list(const irept::subt &, bool is_generic);
  void typecheck_declarations(const irept &decl);
  void typecheck_declaration(const irept &decl);
  void typecheck_object_declaration(const vhdl_object_declarationt &);
  void typecheck_type_declaration(const vhdl_type_declarationt &);
  void typecheck_subtype_declaration(const vhdl_type_declarationt &);

  // concurrent statements
  exprt typecheck_concurrent_statements(const irept &);
  exprt typecheck_concurrent_statement(exprt);
  /// the label of a concurrent statement is a declaration
  void declare_label(irep_idt label, const source_locationt &);
  exprt typecheck_process(exprt);

  // sequential statements
  codet typecheck_code(exprt);
  codet typecheck_block(exprt);
  codet typecheck_assert(exprt);
  codet typecheck_assign(exprt, bool is_signal);
  codet typecheck_selected_assign(exprt, bool is_signal);
  codet typecheck_if(exprt);
  codet typecheck_case(exprt);
  codet typecheck_for(exprt);

  /// a condition, with the implicit condition operator ??
  exprt typecheck_condition(exprt);

  // IEEE 1076-2008 10.9: the choices of a case statement cover every
  // value of the type of the selector exactly once
  struct choicest
  {
    struct intervalt
    {
      mp_integer low, high;
      source_locationt source_location;
    };

    std::vector<intervalt> intervals;
    bool others = false;
  };

  /// the conditions of the alternatives; the last one is true
  std::vector<exprt> case_conditions(
    const exprt &selector,
    const irept::subt &alternatives,
    const source_locationt &);
  /// the condition for the choices of one alternative
  exprt
  case_condition(const exprt &selector, const irept::subt &choices, choicest &);
  void check_choices(choicest &, const typet &, const source_locationt &);
  std::optional<mp_integer> position_number(const exprt &) const;
  static std::optional<mp_integer> number_of_values(const typet &);
  static std::string value_to_string(const mp_integer &, const typet &);

  // types
  typet typecheck_type(const typet &);
  typet typecheck_subtype_indication(const typet &);
  typet typecheck_type_mark(const exprt &name);
  vhdl_ranget typecheck_range(const exprt &);
  /// type check an expression that must be a static integer
  mp_integer typecheck_static_integer(const exprt &);
  /// the value of a type checked expression, if it is static
  std::optional<mp_integer> constant_value(const exprt &) const;

  /// the default initial value of a type (T'left), or nil
  exprt default_value(const typet &);

  // expressions
  exprt typecheck_expr(exprt);
  exprt typecheck_expr_rec(exprt);
  exprt typecheck_symbol(symbol_exprt);
  exprt typecheck_indexed(exprt);
  exprt typecheck_slice(exprt);
  exprt typecheck_attribute(exprt);
  /// the functions of the IEEE packages that are supported
  bool is_known_function(irep_idt name) const;
  exprt typecheck_function_call(
    irep_idt name,
    exprt::operandst arguments,
    const source_locationt &);
  exprt typecheck_type_conversion(exprt, const typet &);
  exprt typecheck_binary(exprt);
  exprt typecheck_concatenation(exprt, exprt, const source_locationt &);
  /// the operators of the numeric packages on vectors
  exprt
  typecheck_numeric_binary(irep_idt id, exprt, exprt, const source_locationt &);
  bool has_numeric_operators(const typet &) const;
  /// unsigned or signed, for the vectors with numeric operators
  typet numeric_type_of(const typet &) const;
  exprt typecheck_unary(exprt);
  exprt typecheck_aggregate(exprt, const typet &);
  /// the elements of an array aggregate, from the low index
  std::vector<exprt>
  aggregate_elements(const vhdl_aggregate_exprt &, const vhdl_array_typet &);

  /// implicit conversion of universal literals, and type matching
  exprt convert_to(exprt, const typet &);
  /// the value of an integer literal
  static mp_integer integer_literal_value(const constant_exprt &);
  /// the type of a literal without a typed context
  exprt literal_with_default_type(exprt);
  /// convert universal literals to the type of the other operand
  void match_literals(exprt &, exprt &);
  /// make the types of two operands match; an error if they differ
  void match_types(exprt &, exprt &);

  /// IEEE 1076-2008 8.4: a static index must be in the index range
  void check_index(
    const exprt &index,
    const vhdl_array_typet &,
    const source_locationt &);
  /// IEEE 1076-2008 5.2.1: a static value must be in the range
  void check_range(
    const exprt &,
    const vhdl_integer_typet &,
    const source_locationt &);
  /// an array value from element literals, e.g., a string literal
  exprt array_from_literals(
    const std::string &literals,
    const vhdl_array_typet &,
    const source_locationt &);

  // Scopes. IEEE 1076-2008 12.3: a declaration in an inner declarative
  // region hides a homograph in an outer region, whatever its kind;
  // enumeration literals may be overloaded. Statement labels are
  // declarations in the enclosing region (IEEE 1076-2008 12.1).
  struct declarationt
  {
    enum kindt
    {
      OBJECT,
      CONSTANT,
      TYPE,
      LITERALS,
      LABEL
    } kind;

    irep_idt symbol;             // OBJECT: the symbol table identifier
    exprt value;                 // CONSTANT
    typet type;                  // TYPE
    std::vector<exprt> literals; // LITERALS: the overloaded literals
  };

  struct scopet
  {
    irep_idt prefix;                               // for new symbols
    std::map<irep_idt, declarationt> declarations; // lower-case base name
  };

  std::vector<scopet> scopes;

  void push_scope(irep_idt prefix)
  {
    scopes.push_back(scopet{prefix, {}});
  }

  void pop_scope()
  {
    scopes.pop_back();
  }

  scopet &current_scope()
  {
    return scopes.back();
  }

  /// lower-case identifier
  static irep_idt to_lower(irep_idt);

  /// find the innermost declaration of the given name
  std::optional<declarationt> lookup(irep_idt lower_case_name) const;

  /// add a declaration to the current scope; an error if the name
  /// is already declared there, except for enumeration literals
  void declare(irep_idt base_name, declarationt, const source_locationt &);

  std::optional<typet> lookup_type(irep_idt lower_case_name) const;
  std::optional<exprt> lookup_constant(irep_idt lower_case_name) const;
  const symbolt *lookup_object(irep_idt lower_case_name) const;

  /// add a symbol for an object, in the current scope
  symbolt &
  add_object(irep_idt base_name, const typet &, const source_locationt &);

  /// the names of the packages in use clauses, lower case
  std::set<irep_idt> packages_used;
  void collect_use_clauses();
  bool uses_package(irep_idt name) const
  {
    return packages_used.count(name) != 0;
  }

  void add_predefined_types();

  unsigned process_counter = 0;
};

#endif
