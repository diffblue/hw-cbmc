/*******************************************************************\

Module: VHDL Expressions

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// VHDL Expressions
///
/// The VHDL-specific expressions and statements produced by the parser.
/// They are resolved during type checking into the generic CBMC
/// expressions, with the exception of vhdl_signal_assignt and
/// vhdl_processt, which the synthesis consumes.

#ifndef CPROVER_VHDL_VHDL_EXPR_H
#define CPROVER_VHDL_VHDL_EXPR_H

#include <util/std_code.h>
#include <util/std_expr.h>

/// IEEE 1076-2008 5.2.1: a range, given as left and right bounds and
/// a direction, to or downto
class vhdl_range_exprt : public binary_exprt
{
public:
  vhdl_range_exprt(exprt _left, irep_idt _direction, exprt _right)
    : binary_exprt(std::move(_left), ID_range, std::move(_right), typet{})
  {
    set(ID_direction, _direction);
  }

  const exprt &left() const
  {
    return op0();
  }

  const exprt &right() const
  {
    return op1();
  }

  /// ID_to or ID_vhdl_downto
  irep_idt direction() const
  {
    return get(ID_direction);
  }
};

inline const vhdl_range_exprt &to_vhdl_range_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_range);
  vhdl_range_exprt::check(expr);
  return static_cast<const vhdl_range_exprt &>(expr);
}

inline vhdl_range_exprt &to_vhdl_range_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_range);
  vhdl_range_exprt::check(expr);
  return static_cast<vhdl_range_exprt &>(expr);
}

/// IEEE 1076-2008 6.5.7.1: an association element, formal => actual;
/// the formal is nil for positional association
class vhdl_associationt : public expr_protectedt
{
public:
  vhdl_associationt(exprt _formal, exprt _actual)
    : expr_protectedt(ID_vhdl_association, typet{})
  {
    add(ID_vhdl_formal) = std::move(_formal);
    add(ID_vhdl_actual) = std::move(_actual);
  }

  const exprt &formal() const
  {
    return static_cast<const exprt &>(find(ID_vhdl_formal));
  }

  const exprt &actual() const
  {
    return static_cast<const exprt &>(find(ID_vhdl_actual));
  }

  bool is_named() const
  {
    return formal().is_not_nil();
  }
};

inline const vhdl_associationt &to_vhdl_association(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_vhdl_association);
  return static_cast<const vhdl_associationt &>(expr);
}

/// IEEE 1076-2008 8.4, 8.5, 9.3.4, 9.3.6: an indexed name, a function
/// call, or a type conversion, which cannot be told apart syntactically.
/// Operand 0 is the prefix, the other operands are the arguments,
/// as association elements.
class vhdl_indexed_exprt : public exprt
{
public:
  explicit vhdl_indexed_exprt(exprt _prefix) : exprt(ID_vhdl_indexed, typet{})
  {
    add_to_operands(std::move(_prefix));
  }

  const exprt &prefix() const
  {
    return operands().front();
  }

  exprt &prefix()
  {
    return operands().front();
  }

  /// the arguments, as vhdl_associationt
  std::size_t number_of_arguments() const
  {
    return operands().size() - 1;
  }

  const vhdl_associationt &argument(std::size_t i) const
  {
    return to_vhdl_association(operands()[i + 1]);
  }

  void add_argument(vhdl_associationt association)
  {
    add_to_operands(std::move(association));
  }
};

inline const vhdl_indexed_exprt &to_vhdl_indexed_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_vhdl_indexed);
  DATA_INVARIANT(!expr.operands().empty(), "indexed name must have a prefix");
  return static_cast<const vhdl_indexed_exprt &>(expr);
}

inline vhdl_indexed_exprt &to_vhdl_indexed_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_vhdl_indexed);
  DATA_INVARIANT(!expr.operands().empty(), "indexed name must have a prefix");
  return static_cast<vhdl_indexed_exprt &>(expr);
}

/// IEEE 1076-2008 8.5: a slice, prefix(range)
class vhdl_slice_exprt : public binary_exprt
{
public:
  vhdl_slice_exprt(exprt _prefix, exprt _range)
    : binary_exprt(
        std::move(_prefix),
        ID_vhdl_slice,
        std::move(_range),
        typet{})
  {
  }

  const exprt &prefix() const
  {
    return op0();
  }

  exprt &prefix()
  {
    return op0();
  }

  /// a vhdl_range_exprt, or a range attribute
  const exprt &range() const
  {
    return op1();
  }
};

inline const vhdl_slice_exprt &to_vhdl_slice_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_vhdl_slice);
  vhdl_slice_exprt::check(expr);
  return static_cast<const vhdl_slice_exprt &>(expr);
}

inline vhdl_slice_exprt &to_vhdl_slice_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_vhdl_slice);
  vhdl_slice_exprt::check(expr);
  return static_cast<vhdl_slice_exprt &>(expr);
}

/// IEEE 1076-2008 8.3: a selected name that denotes a record element,
/// after type checking; as member_exprt, but with a VHDL record type
class vhdl_member_exprt : public unary_exprt
{
public:
  vhdl_member_exprt(exprt _compound, irep_idt _component_name, typet _type)
    : unary_exprt(ID_member, std::move(_compound), std::move(_type))
  {
    set(ID_component_name, _component_name);
  }

  const exprt &compound() const
  {
    return op();
  }

  irep_idt get_component_name() const
  {
    return get(ID_component_name);
  }
};

inline const vhdl_member_exprt &to_vhdl_member_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_member);
  vhdl_member_exprt::check(expr);
  return static_cast<const vhdl_member_exprt &>(expr);
}

/// IEEE 1076-2008 8.6: an attribute name, prefix'attribute
class vhdl_attribute_exprt : public unary_exprt
{
public:
  vhdl_attribute_exprt(exprt _prefix, irep_idt _attribute)
    : unary_exprt(ID_vhdl_attribute, std::move(_prefix), typet{})
  {
    set(ID_identifier, _attribute);
  }

  const exprt &prefix() const
  {
    return op();
  }

  exprt &prefix()
  {
    return op();
  }

  /// the attribute designator, as written
  irep_idt attribute() const
  {
    return get(ID_identifier);
  }
};

inline const vhdl_attribute_exprt &to_vhdl_attribute_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_vhdl_attribute);
  vhdl_attribute_exprt::check(expr);
  return static_cast<const vhdl_attribute_exprt &>(expr);
}

inline vhdl_attribute_exprt &to_vhdl_attribute_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_vhdl_attribute);
  vhdl_attribute_exprt::check(expr);
  return static_cast<vhdl_attribute_exprt &>(expr);
}

/// IEEE 1076-2008 9.3.5: a qualified expression, type_mark'(expr)
class vhdl_qualified_exprt : public binary_exprt
{
public:
  vhdl_qualified_exprt(exprt _type_mark, exprt _op)
    : binary_exprt(
        std::move(_type_mark),
        ID_vhdl_qualified,
        std::move(_op),
        typet{})
  {
  }

  const exprt &type_mark() const
  {
    return op0();
  }

  const exprt &op() const
  {
    return op1();
  }
};

inline const vhdl_qualified_exprt &to_vhdl_qualified_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_vhdl_qualified);
  vhdl_qualified_exprt::check(expr);
  return static_cast<const vhdl_qualified_exprt &>(expr);
}

/// IEEE 1076-2008 9.3.3.1: an element association in an aggregate,
/// choices => value; the choices are empty for positional association
class vhdl_element_associationt : public unary_exprt
{
public:
  explicit vhdl_element_associationt(exprt _value)
    : unary_exprt(ID_vhdl_element_association, std::move(_value), typet{})
  {
    add(ID_vhdl_choices);
  }

  /// each choice is an expression, a vhdl_range_exprt, or ID_vhdl_others
  const irept::subt &choices() const
  {
    return find(ID_vhdl_choices).get_sub();
  }

  irept::subt &choices()
  {
    return add(ID_vhdl_choices).get_sub();
  }

  bool is_positional() const
  {
    return choices().empty();
  }

  const exprt &value() const
  {
    return op();
  }
};

inline const vhdl_element_associationt &
to_vhdl_element_association(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_vhdl_element_association);
  vhdl_element_associationt::check(expr);
  return static_cast<const vhdl_element_associationt &>(expr);
}

/// IEEE 1076-2008 9.3.3: an aggregate; the operands are
/// vhdl_element_associationt
class vhdl_aggregate_exprt : public exprt
{
public:
  vhdl_aggregate_exprt() : exprt(ID_vhdl_aggregate, typet{})
  {
  }

  void add_association(vhdl_element_associationt association)
  {
    add_to_operands(std::move(association));
  }

  const vhdl_element_associationt &association(std::size_t i) const
  {
    return to_vhdl_element_association(operands()[i]);
  }
};

inline const vhdl_aggregate_exprt &to_vhdl_aggregate_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_vhdl_aggregate);
  return static_cast<const vhdl_aggregate_exprt &>(expr);
}

/// IEEE 1076-2008 5.2.2.1: an overloaded enumeration literal, produced
/// by the type checker when the literal is declared by more than one
/// enumeration type. The operands are the candidates; the type is
/// determined by the context.
class vhdl_overloaded_literal_exprt : public exprt
{
public:
  vhdl_overloaded_literal_exprt(
    irep_idt _identifier,
    exprt::operandst _candidates)
    : exprt(
        ID_vhdl_overloaded_literal,
        typet{ID_vhdl_overloaded_literal},
        std::move(_candidates))
  {
    set(ID_identifier, _identifier);
  }

  /// the literal, as written
  irep_idt identifier() const
  {
    return get(ID_identifier);
  }

  const exprt::operandst &candidates() const
  {
    return operands();
  }
};

inline const vhdl_overloaded_literal_exprt &
to_vhdl_overloaded_literal_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_vhdl_overloaded_literal);
  return static_cast<const vhdl_overloaded_literal_exprt &>(expr);
}

/// IEEE 1076-2008 15.5.1: a physical literal, e.g. 10 ns
class vhdl_physical_literal_exprt : public nullary_exprt
{
public:
  vhdl_physical_literal_exprt(irep_idt _value, irep_idt _unit)
    : nullary_exprt(ID_vhdl_physical, typet{})
  {
    set(ID_value, _value);
    set(ID_identifier, _unit);
  }

  irep_idt value() const
  {
    return get(ID_value);
  }

  irep_idt unit() const
  {
    return get(ID_identifier);
  }
};

/// IEEE 1076-2008 10.1, 11.1: a sequential or concurrent statement.
/// Any statement may be labelled; the label is set by the parser.
class vhdl_statementt : public exprt
{
public:
  vhdl_statementt(irep_idt _id, operandst _operands)
    : exprt(std::move(_id), typet{}, std::move(_operands))
  {
  }

  /// the label, or empty
  irep_idt label() const
  {
    return get(ID_label);
  }

  bool has_label() const
  {
    return !label().empty();
  }

  void set_label(irep_idt _label)
  {
    set(ID_label, _label);
  }
};

/// Any statement produced by the parser; there is no check on the id,
/// as there are many kinds of statements.
inline const vhdl_statementt &to_vhdl_statement(const exprt &expr)
{
  return static_cast<const vhdl_statementt &>(expr);
}

inline vhdl_statementt &to_vhdl_statement(exprt &expr)
{
  return static_cast<vhdl_statementt &>(expr);
}

/// IEEE 1076-2008 10.5, 11.6: a signal assignment, sequential or
/// concurrent. The value is an expression, or nested if expressions for
/// the conditional form, with a nil else branch when there is none.
class vhdl_signal_assignt : public vhdl_statementt
{
public:
  vhdl_signal_assignt(exprt _target, exprt _value)
    : vhdl_statementt(
        ID_vhdl_signal_assign,
        {std::move(_target), std::move(_value)})
  {
  }

  const exprt &target() const
  {
    return op0();
  }

  const exprt &value() const
  {
    return op1();
  }
};

inline const vhdl_signal_assignt &to_vhdl_signal_assign(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_vhdl_signal_assign);
  DATA_INVARIANT(
    expr.operands().size() == 2, "signal assignment has target and value");
  return static_cast<const vhdl_signal_assignt &>(expr);
}

/// IEEE 1076-2008 10.5.4, 10.6.2.3, 11.6: a selected signal or variable
/// assignment, with ... select target <= ...; the alternatives are
/// case items, each with choices and a value
class vhdl_selected_assignt : public vhdl_statementt
{
public:
  vhdl_selected_assignt(exprt _target, exprt _selector, bool _is_variable)
    : vhdl_statementt(
        ID_vhdl_selected_assign,
        {std::move(_target), std::move(_selector)})
  {
    add(ID_vhdl_choices);
    if(_is_variable)
      set(ID_vhdl_variable, true);
  }

  const exprt &target() const
  {
    return op0();
  }

  const exprt &selector() const
  {
    return op1();
  }

  bool is_variable_assignment() const
  {
    return get_bool(ID_vhdl_variable);
  }

  /// the alternatives, each a case item with choices and the value
  /// as operand 0
  const irept::subt &alternatives() const
  {
    return find(ID_vhdl_choices).get_sub();
  }

  irept::subt &alternatives()
  {
    return add(ID_vhdl_choices).get_sub();
  }
};

inline const vhdl_selected_assignt &to_vhdl_selected_assign(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_vhdl_selected_assign);
  DATA_INVARIANT(
    expr.operands().size() == 2, "selected assignment has target and selector");
  return static_cast<const vhdl_selected_assignt &>(expr);
}

/// IEEE 1076-2008 11.3: a process statement. Operand 0 is the body,
/// a block of sequential statements.
class vhdl_processt : public vhdl_statementt
{
public:
  vhdl_processt(exprt _sensitivity, irept _declarations, exprt _body)
    : vhdl_statementt(ID_process, {std::move(_body)})
  {
    add(ID_vhdl_sensitivity) = std::move(_sensitivity);
    add(ID_decl) = std::move(_declarations);
  }

  /// the sensitivity list: nil, ID_all, or a list of names
  const exprt &sensitivity() const
  {
    return static_cast<const exprt &>(find(ID_vhdl_sensitivity));
  }

  exprt &sensitivity()
  {
    return static_cast<exprt &>(add(ID_vhdl_sensitivity));
  }

  const irept &declarations() const
  {
    return find(ID_decl);
  }

  const exprt &body() const
  {
    return op0();
  }

  exprt &body()
  {
    return op0();
  }
};

inline const vhdl_processt &to_vhdl_process(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_process);
  DATA_INVARIANT(expr.operands().size() == 1, "process has a body");
  return static_cast<const vhdl_processt &>(expr);
}

inline vhdl_processt &to_vhdl_process(exprt &expr)
{
  PRECONDITION(expr.id() == ID_process);
  DATA_INVARIANT(expr.operands().size() == 1, "process has a body");
  return static_cast<vhdl_processt &>(expr);
}

/// IEEE 1076-2008 6.4.2, 6.5.2, 5.3.3: a declaration of a list of
/// identifiers with a subtype indication: a signal, constant or
/// variable declaration, an interface element (a port or generic),
/// or a record element declaration. The id is ID_signal, ID_constant,
/// ID_vhdl_variable, ID_port or ID_component.
class vhdl_object_declarationt : public exprt
{
public:
  /// the identifiers, as symbol expressions
  const irept::subt &declarators() const
  {
    return find(ID_vhdl_declarators).get_sub();
  }

  irept::subt &declarators()
  {
    return add(ID_vhdl_declarators).get_sub();
  }

  /// the subtype indication; this is exprt::type()
  const typet &subtype_indication() const
  {
    return type();
  }

  /// the initial value, or nil
  const exprt &initial_value() const
  {
    return static_cast<const exprt &>(find(ID_init));
  }

  /// interface elements: ID_input, ID_output, ID_inout or ID_buffer
  irep_idt mode() const
  {
    return get(ID_mode);
  }

  /// interface elements: ID_signal, ID_constant, ID_vhdl_variable,
  /// or ID_nil when not given
  irep_idt object_class() const
  {
    return get(ID_class);
  }
};

inline const vhdl_object_declarationt &
to_vhdl_object_declaration(const irept &irep)
{
  return static_cast<const vhdl_object_declarationt &>(irep);
}

/// IEEE 1076-2008 6.2, 6.3: a type or subtype declaration,
/// type name is ...; the id is ID_vhdl_type_decl or ID_vhdl_subtype_decl.
/// The type definition is exprt::type().
class vhdl_type_declarationt : public exprt
{
public:
  const symbol_exprt &name() const
  {
    return to_symbol_expr(static_cast<const exprt &>(find(ID_name)));
  }

  /// the type definition, or the subtype indication
  const typet &definition() const
  {
    return type();
  }
};

inline const vhdl_type_declarationt &to_vhdl_type_declaration(const irept &irep)
{
  PRECONDITION(
    irep.id() == ID_vhdl_type_decl || irep.id() == ID_vhdl_subtype_decl);
  return static_cast<const vhdl_type_declarationt &>(irep);
}

/// IEEE 1076-2008 10.3, 11.5: an assertion statement, sequential or
/// concurrent, assert condition report expr severity level
class vhdl_assertt : public vhdl_statementt
{
public:
  const exprt &condition() const
  {
    return op0();
  }

  exprt &condition()
  {
    return op0();
  }

  /// the report expression, or nil
  const exprt &report() const
  {
    return static_cast<const exprt &>(find(ID_vhdl_report));
  }
};

inline const vhdl_assertt &to_vhdl_assert(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_assert);
  DATA_INVARIANT(expr.operands().size() == 1, "assertion has a condition");
  return static_cast<const vhdl_assertt &>(expr);
}

inline vhdl_assertt &to_vhdl_assert(exprt &expr)
{
  PRECONDITION(expr.id() == ID_assert);
  DATA_INVARIANT(expr.operands().size() == 1, "assertion has a condition");
  return static_cast<vhdl_assertt &>(expr);
}

/// The type checked assertion, with a boolean condition, the label
/// and the report string
class vhdl_code_assertt : public codet
{
public:
  vhdl_code_assertt(exprt _condition, irep_idt _label, exprt _report)
    : codet(ID_assert, {std::move(_condition)})
  {
    set(ID_label, _label);
    add(ID_vhdl_report) = std::move(_report);
  }

  const exprt &condition() const
  {
    return op0();
  }

  irep_idt label() const
  {
    return get(ID_label);
  }

  /// a string literal, or nil
  const exprt &report() const
  {
    return static_cast<const exprt &>(find(ID_vhdl_report));
  }
};

inline const vhdl_code_assertt &to_vhdl_code_assert(const codet &code)
{
  PRECONDITION(code.get_statement() == ID_assert);
  return static_cast<const vhdl_code_assertt &>(code);
}

/// The type checked signal or variable assignment, with the target and
/// the value; the statement is ID_vhdl_signal_assign or ID_assign
class vhdl_code_assignt : public codet
{
public:
  vhdl_code_assignt(bool _is_signal, exprt _target, exprt _value)
    : codet(
        _is_signal ? ID_vhdl_signal_assign : ID_assign,
        {std::move(_target), std::move(_value)})
  {
  }

  const exprt &target() const
  {
    return op0();
  }

  /// the value; nil for `unaffected`, or nested if expressions for a
  /// conditional assignment
  const exprt &value() const
  {
    return op1();
  }

  bool is_signal_assignment() const
  {
    return get_statement() == ID_vhdl_signal_assign;
  }
};

inline const vhdl_code_assignt &to_vhdl_code_assign(const codet &code)
{
  PRECONDITION(
    code.get_statement() == ID_assign ||
    code.get_statement() == ID_vhdl_signal_assign);
  DATA_INVARIANT(
    code.operands().size() == 2, "assignment has target and value");
  return static_cast<const vhdl_code_assignt &>(code);
}

/// IEEE 1076-2008 10.9, 10.5.4: an alternative of a case statement,
/// when choices => body, or of a selected assignment, value when choices
class vhdl_case_alternativet : public unary_exprt
{
public:
  /// each choice is an expression, a vhdl_range_exprt, or ID_vhdl_others
  const irept::subt &choices() const
  {
    return find(ID_vhdl_choices).get_sub();
  }

  /// the sequence of statements, or the value
  const exprt &body() const
  {
    return op();
  }
};

inline const vhdl_case_alternativet &to_vhdl_case_alternative(const irept &irep)
{
  PRECONDITION(irep.id() == ID_case_item);
  auto &expr = static_cast<const exprt &>(irep);
  vhdl_case_alternativet::check(expr);
  return static_cast<const vhdl_case_alternativet &>(expr);
}

/// IEEE 1076-2008 10.9: a case statement; the operand is the selector
class vhdl_case_statementt : public vhdl_statementt
{
public:
  const exprt &selector() const
  {
    return op0();
  }

  /// the alternatives, as vhdl_case_alternativet
  const irept::subt &alternatives() const
  {
    return find(ID_case_item).get_sub();
  }
};

inline const vhdl_case_statementt &to_vhdl_case_statement(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_switch_case);
  DATA_INVARIANT(expr.operands().size() == 1, "case statement has a selector");
  return static_cast<const vhdl_case_statementt &>(expr);
}

/// IEEE 1076-2008 10.10: a for loop; the operand is the body
class vhdl_for_statementt : public vhdl_statementt
{
public:
  const symbol_exprt &loop_variable() const
  {
    return to_symbol_expr(
      static_cast<const exprt &>(find(ID_vhdl_loop_variable)));
  }

  /// a discrete range: a vhdl_range_exprt, a range attribute,
  /// or a subtype indication
  const exprt &range() const
  {
    return static_cast<const exprt &>(find(ID_range));
  }

  const exprt &body() const
  {
    return op0();
  }
};

inline const vhdl_for_statementt &to_vhdl_for_statement(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_for);
  DATA_INVARIANT(expr.operands().size() == 1, "for loop has a body");
  return static_cast<const vhdl_for_statementt &>(expr);
}

#endif // CPROVER_VHDL_VHDL_EXPR_H
