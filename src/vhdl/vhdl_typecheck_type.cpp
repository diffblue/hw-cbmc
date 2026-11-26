/*******************************************************************\

Module: VHDL Type Checking of Types

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// VHDL Type Checking of Types

#include "vhdl_typecheck_class.h"

#include <util/arith_tools.h>

/// The value of a type checked integer expression, if it is static
/// (IEEE 1076-2008 9.4.2); constants have been inlined, so this
/// evaluates the arithmetic operators on constants.
std::optional<mp_integer>
vhdl_typecheckt::constant_value(const exprt &expr) const
{
  if(!is_vhdl_integer_type(expr.type()))
    return {};

  auto id = expr.id();

  if(id == ID_constant)
    return vhdl_integer_value(to_constant_expr(expr));
  else if(id == ID_typecast)
  {
    // between integer subtypes
    return constant_value(to_typecast_expr(expr).op());
  }
  else if(id == ID_unary_minus || id == ID_abs)
  {
    auto op = constant_value(to_unary_expr(expr).op());
    if(!op.has_value())
      return {};
    return id == ID_unary_minus ? -*op : (*op < 0 ? -*op : *op);
  }
  else if(
    id == ID_plus || id == ID_minus || id == ID_mult || id == ID_div ||
    id == ID_mod || id == ID_vhdl_rem)
  {
    auto &binary = to_binary_expr(expr);
    auto lhs = constant_value(binary.lhs());
    auto rhs = constant_value(binary.rhs());
    if(!lhs.has_value() || !rhs.has_value())
      return {};

    if(id == ID_plus)
      return *lhs + *rhs;
    else if(id == ID_minus)
      return *lhs - *rhs;
    else if(id == ID_mult)
      return *lhs * *rhs;

    if(*rhs == 0)
      return {}; // division by zero is a run-time error

    // IEEE 1076-2008 9.2.7: / and rem truncate towards zero; mod has
    // the sign of the right operand
    auto quotient = *lhs / *rhs; // mp_integer truncates towards zero
    auto remainder = *lhs - quotient * *rhs;

    if(id == ID_div)
      return quotient;
    else if(id == ID_vhdl_rem)
      return remainder;
    else // mod
    {
      if(remainder != 0 && ((remainder < 0) != (*rhs < 0)))
        remainder += *rhs;
      return remainder;
    }
  }
  else
    return {};
}

/// IEEE 1076-2008 9.4.2: a static expression over literals and constants
mp_integer vhdl_typecheckt::typecheck_static_integer(const exprt &expr)
{
  auto typed = typecheck_expr(expr);

  if(is_vhdl_universal_type(typed.type()))
    typed = convert_to(typed, vhdl_integer_type());

  if(!is_vhdl_integer_type(typed.type()))
    throw errort{}.with_location(expr.source_location())
      << "expected an integer expression, got "
      << vhdl_type_to_string(typed.type());

  auto value = constant_value(typed);

  if(!value.has_value())
    throw errort{}.with_location(expr.source_location())
      << "expected a static expression";

  return *value;
}

/// A range, given as two bounds with a direction, or as a range
/// attribute, e.g., v'range.
vhdl_ranget vhdl_typecheckt::typecheck_range(const exprt &range)
{
  if(range.id() == ID_range)
  {
    auto &range_expr = to_vhdl_range_expr(range);
    vhdl_ranget result;
    result.left = typecheck_static_integer(range_expr.left());
    result.right = typecheck_static_integer(range_expr.right());
    result.direction = to_vhdl_direction(range_expr.direction());
    return result;
  }
  else if(
    range.id() == ID_vhdl_attribute &&
    (to_lower(to_vhdl_attribute_expr(range).attribute()) == "range" ||
     to_lower(to_vhdl_attribute_expr(range).attribute()) == "reverse_range"))
  {
    auto &attribute_expr = to_vhdl_attribute_expr(range);
    auto &prefix = attribute_expr.prefix();

    // the prefix may be a type or an object
    std::optional<typet> type;

    if(prefix.id() == ID_symbol)
      type = lookup_type(to_lower(to_symbol_expr(prefix).get_identifier()));

    if(!type.has_value())
      type = typecheck_expr(prefix).type();

    if(
      type->id() != ID_vhdl_array ||
      !to_vhdl_array_type(*type).is_constrained())
      throw errort{}.with_location(range.source_location())
        << "range attribute requires a constrained array type";

    auto result = to_vhdl_array_type(*type).range();

    if(to_lower(attribute_expr.attribute()) == "reverse_range")
    {
      std::swap(result.left, result.right);
      result.direction = result.direction == vhdl_directiont::TO
                           ? vhdl_directiont::DOWNTO
                           : vhdl_directiont::TO;
    }

    return result;
  }
  else if(range.id() == ID_vhdl_subtype_indication)
  {
    // e.g., integer range 0 to 7
    auto type = typecheck_subtype_indication(
      static_cast<const typet &>(static_cast<const irept &>(range)));
    if(!is_vhdl_integer_type(type))
      throw errort{}.with_location(range.source_location())
        << "expected a range";
    return to_vhdl_integer_type(type).range();
  }
  else
    throw errort{}.with_location(range.source_location()) << "expected a range";
}

/// The name of a type, possibly a selected name such as
/// ieee.std_logic_1164.std_logic; only the last component is used.
typet vhdl_typecheckt::typecheck_type_mark(const exprt &name)
{
  irep_idt base_name;

  if(name.id() == ID_symbol)
    base_name = to_symbol_expr(name).get_identifier();
  else if(name.id() == ID_member)
    base_name = to_member_expr(name).get_component_name();
  else
    throw errort{}.with_location(name.source_location())
      << "expected a type name";

  auto type = lookup_type(to_lower(base_name));

  if(!type.has_value())
    throw errort{}.with_location(name.source_location())
      << "unknown type `" << base_name << "'";

  return *type;
}

/// IEEE 1076-2008 6.3: a type mark with an optional constraint
typet vhdl_typecheckt::typecheck_subtype_indication(const typet &type)
{
  if(type.id() != ID_vhdl_subtype_indication)
    return typecheck_type(type);

  auto &subtype_indication = to_vhdl_subtype_indication(type);
  auto base = typecheck_type_mark(subtype_indication.type_mark());

  auto &range_constraint = subtype_indication.range_constraint();
  auto &index_constraint = subtype_indication.index_constraint();

  if(range_constraint.is_not_nil())
  {
    // e.g., integer range 0 to 7
    if(!is_vhdl_integer_type(base))
      throw errort{}.with_location(type.source_location())
        << "range constraint requires a scalar type";

    auto range = typecheck_range(range_constraint);

    // IEEE 1076-2008 5.2.1: the range must be within the base subtype
    auto base_range = to_vhdl_integer_type(base).range();
    if(
      range.length() != 0 &&
      (range.low() < base_range.low() || range.high() > base_range.high()))
      throw errort{}.with_location(type.source_location())
        << "the range " << range.low() << " to " << range.high()
        << " is outside of the range of " << to_vhdl_integer_type(base).name();

    auto result = to_vhdl_integer_type(base);
    result.set_range(range);
    return std::move(result);
  }
  else if(!index_constraint.empty())
  {
    // e.g., std_logic_vector(7 downto 0)
    if(index_constraint.size() != 1)
      throw errort{}.with_location(type.source_location())
        << "only one-dimensional arrays are supported";

    auto range =
      typecheck_range(static_cast<const exprt &>(index_constraint.front()));

    if(base.id() == ID_vhdl_array && !to_vhdl_array_type(base).is_constrained())
      return vhdl_constrained_array_type(to_vhdl_array_type(base), range);
    else
      throw errort{}.with_location(type.source_location())
        << "index constraint requires an unconstrained array type";
  }
  else
  {
    // An unconstrained type is permitted for constants, whose
    // constraint comes from the initial value (IEEE 1076-2008 6.4.2.2);
    // the callers check this.
    return base;
  }
}

/// IEEE 1076-2008 6.2: a type definition. The type gets its name from
/// the declaration.
typet vhdl_typecheckt::typecheck_type(const typet &type)
{
  if(type.id() == ID_vhdl_subtype_indication)
  {
    return typecheck_subtype_indication(type);
  }
  else if(type.id() == ID_enumeration)
  {
    // the literals are lower case
    auto &definition =
      static_cast<const vhdl_enumeration_type_definitiont &>(type);

    irept::subt elements;

    for(auto &element : definition.elements())
    {
      auto &element_expr = static_cast<const exprt &>(element);
      irep_idt literal;

      if(element_expr.id() == ID_symbol)
        literal = to_lower(to_symbol_expr(element_expr).get_identifier());
      else if(element_expr.id() == ID_constant)
      {
        // a character literal, keyed with its quotes
        auto value = id2string(to_constant_expr(element_expr).get_value());
        DATA_INVARIANT(
          value.size() == 1, "character literals have one character");
        literal = vhdl_enumeration_typet::character_literal(value[0]);
      }
      else
        throw errort{}.with_location(element_expr.source_location())
          << "unexpected enumeration literal";

      for(auto &other : elements)
        if(other.id() == literal)
          throw errort{}.with_location(element_expr.source_location())
            << "enumeration literal `" << literal << "' is given twice";

      elements.push_back(irept{literal});
    }

    vhdl_enumeration_typet result{irep_idt{}, std::move(elements)};
    result.add_source_location() = type.source_location();
    return std::move(result);
  }
  else if(type.id() == ID_range)
  {
    // an integer type
    auto &definition = static_cast<const vhdl_integer_type_definitiont &>(type);
    auto range = typecheck_range(definition.range());
    vhdl_integer_typet result{irep_idt{}, range};
    result.add_source_location() = type.source_location();
    return std::move(result);
  }
  else if(type.id() == ID_array)
  {
    auto &definition = static_cast<const vhdl_array_type_definitiont &>(type);
    auto element_type = typecheck_subtype_indication(definition.element_type());

    auto &index_constraint = definition.index_constraint();

    if(index_constraint.size() != 1)
      throw errort{}.with_location(type.source_location())
        << "only one-dimensional arrays are supported";

    auto &index = static_cast<const exprt &>(index_constraint.front());

    if(index.id() == ID_vhdl_unconstrained)
    {
      // e.g., array (natural range <>) of ...; the index subtype gives
      // the left bound and direction of values whose range is not
      // given by the context (IEEE 1076-2008 9.3.2)
      auto index_type =
        typecheck_type_mark(static_cast<const exprt &>(index.find(ID_type)));

      if(index_type.id() != ID_vhdl_integer)
        throw errort{}.with_location(index.source_location())
          << "index subtype must be an integer type, got "
          << vhdl_type_to_string(index_type);

      vhdl_array_typet result{
        irep_idt{}, std::move(element_type), to_vhdl_integer_type(index_type)};
      result.add_source_location() = type.source_location();
      return std::move(result);
    }
    else
    {
      auto range = typecheck_range(index);
      vhdl_array_typet result{irep_idt{}, std::move(element_type), range};
      result.add_source_location() = type.source_location();
      return std::move(result);
    }
  }
  else if(type.id() == ID_struct)
  {
    auto &definition = static_cast<const vhdl_record_type_definitiont &>(type);

    vhdl_record_typet::componentst components;

    for(auto &element_irep : definition.elements())
    {
      auto &element = to_vhdl_object_declaration(element_irep);
      auto element_type =
        typecheck_subtype_indication(element.subtype_indication());

      for(auto &declarator_irep : element.declarators())
      {
        auto &declarator =
          to_symbol_expr(static_cast<const exprt &>(declarator_irep));
        irep_idt name = to_lower(declarator.get_identifier());

        // IEEE 1076-2008 5.3.3 permits unconstrained elements, whose
        // constraint comes from the object; this is not supported
        if(is_unconstrained_array(element_type))
          throw errort{}.with_location(declarator.source_location())
            << "record element `" << name << "' requires a constraint";
        for(auto &c : components)
          if(c.get_name() == name)
            throw errort{}.with_location(declarator.source_location())
              << "record element `" << name << "' is already declared";
        components.emplace_back(name, element_type);
        components.back().set_pretty_name(name);
      }
    }

    vhdl_record_typet result{irep_idt{}, std::move(components)};
    result.add_source_location() = type.source_location();
    return std::move(result);
  }
  else
    throw errort{}.with_location(type.source_location())
      << "unexpected type: " << type.id();
}

/// IEEE 1076-2008 6.4.2.3: the default initial value of an object
/// is T'left. For std_ulogic, this is 'U', which we do not model; the
/// value is left undetermined, given as nil.
exprt vhdl_typecheckt::default_value(const typet &type)
{
  if(type.id() == ID_vhdl_enumeration)
  {
    auto &enumeration_type = to_vhdl_enumeration_type(type);
    if(enumeration_type.base_name() == "std_ulogic")
      return nil_exprt{}; // 'U'
    return constant_exprt{enumeration_type.literal(0), type};
  }
  else if(type.id() == ID_vhdl_integer)
  {
    return vhdl_integer_constant(to_vhdl_integer_type(type).range().left, type);
  }
  else if(type.id() == ID_vhdl_array)
  {
    auto &array_type = to_vhdl_array_type(type);
    auto element_default = default_value(array_type.element_type());
    if(element_default.is_nil())
      return nil_exprt{};
    return unary_exprt{ID_array_of, element_default, array_type};
  }
  else if(type.id() == ID_vhdl_record)
  {
    struct_exprt result{{}, type};
    for(auto &c : to_vhdl_record_type(type).components())
    {
      auto element_default = default_value(c.type());
      if(element_default.is_nil())
        return nil_exprt{};
      result.operands().push_back(std::move(element_default));
    }
    return std::move(result);
  }
  else
    return nil_exprt{};
}
