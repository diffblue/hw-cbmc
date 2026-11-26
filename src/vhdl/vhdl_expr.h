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
  vhdl_range_exprt(exprt _left, const irep_idt &_direction, exprt _right)
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

/// IEEE 1076-2008 8.6: an attribute name, prefix'attribute
class vhdl_attribute_exprt : public unary_exprt
{
public:
  vhdl_attribute_exprt(exprt _prefix, const irep_idt &_attribute)
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

/// IEEE 1076-2008 15.5.1: a physical literal, e.g. 10 ns
class vhdl_physical_literal_exprt : public nullary_exprt
{
public:
  vhdl_physical_literal_exprt(const irep_idt &_value, const irep_idt &_unit)
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

/// IEEE 1076-2008 10.5, 11.6: a signal assignment, sequential or
/// concurrent. The value is an expression, or nested if expressions for
/// the conditional form, with a nil else branch when there is none.
class vhdl_signal_assignt : public binary_exprt
{
public:
  vhdl_signal_assignt(exprt _target, exprt _value)
    : binary_exprt(
        std::move(_target),
        ID_vhdl_signal_assign,
        std::move(_value),
        typet{})
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
  vhdl_signal_assignt::check(expr);
  return static_cast<const vhdl_signal_assignt &>(expr);
}

/// IEEE 1076-2008 10.5.4, 10.6.2.3, 11.6: a selected signal or variable
/// assignment, with ... select target <= ...; the alternatives are
/// case items, each with choices and a value
class vhdl_selected_assignt : public binary_exprt
{
public:
  vhdl_selected_assignt(exprt _target, exprt _selector, bool _is_variable)
    : binary_exprt(
        std::move(_target),
        ID_vhdl_selected_assign,
        std::move(_selector),
        typet{})
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
  vhdl_selected_assignt::check(expr);
  return static_cast<const vhdl_selected_assignt &>(expr);
}

/// IEEE 1076-2008 11.3: a process statement. Operand 0 is the body,
/// a block of sequential statements.
class vhdl_processt : public unary_exprt
{
public:
  vhdl_processt(exprt _sensitivity, irept _declarations, exprt _body)
    : unary_exprt(ID_process, std::move(_body), typet{})
  {
    add(ID_vhdl_sensitivity) = std::move(_sensitivity);
    add(ID_decl) = std::move(_declarations);
  }

  /// the sensitivity list: nil, ID_all, or a list of names
  const exprt &sensitivity() const
  {
    return static_cast<const exprt &>(find(ID_vhdl_sensitivity));
  }

  const irept &declarations() const
  {
    return find(ID_decl);
  }

  const exprt &body() const
  {
    return op();
  }

  exprt &body()
  {
    return op();
  }
};

inline const vhdl_processt &to_vhdl_process(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_process);
  vhdl_processt::check(expr);
  return static_cast<const vhdl_processt &>(expr);
}

inline vhdl_processt &to_vhdl_process(exprt &expr)
{
  PRECONDITION(expr.id() == ID_process);
  vhdl_processt::check(expr);
  return static_cast<vhdl_processt &>(expr);
}

#endif // CPROVER_VHDL_VHDL_EXPR_H
