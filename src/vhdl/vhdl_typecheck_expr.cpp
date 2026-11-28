/*******************************************************************\

Module: VHDL Type Checking of Expressions

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// VHDL Type Checking of Expressions
///
/// The expressions produced here have VHDL types (vhdl_types.h). The
/// operators are the generic CBMC operators applied to operands of VHDL
/// types, with the result type as given by IEEE 1076-2008 and the
/// numeric packages; vhdl_lowering maps them to CBMC types and
/// operators after synthesis.

#include "vhdl_typecheck_class.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/mathematical_expr.h>

#include <algorithm>
#include <map>

exprt vhdl_typecheckt::typecheck_expr(exprt expr)
{
  auto source_location = expr.source_location();
  auto result = typecheck_expr_rec(std::move(expr));
  if(result.source_location().is_nil())
    result.add_source_location() = source_location;
  return result;
}

exprt vhdl_typecheckt::typecheck_expr_rec(exprt expr)
{
  if(expr.id() == ID_symbol)
  {
    return typecheck_symbol(to_symbol_expr(expr));
  }
  else if(expr.id() == ID_constant)
  {
    // The literals are universal, and get their type from the context;
    // this is done in convert_to.
    auto type_id = expr.type().id();

    if(
      type_id == ID_natural || type_id == ID_char || type_id == ID_string ||
      type_id == ID_vhdl_bit_string || type_id == ID_real)
    {
      return expr;
    }
    else if(type_id == ID_nullptr)
      return expr; // the access type comes from the context
    else
      return expr; // already typed
  }
  else if(expr.id() == ID_vhdl_physical)
  {
    return typecheck_physical_literal(to_vhdl_physical_literal_expr(expr));
  }
  else if(expr.id() == ID_vhdl_allocator)
  {
    // IEEE 1076-2008 9.3.7: new type_mark; the access type is anonymous
    // and takes its name from the context in convert_to
    auto designated_type =
      typecheck_type_mark(to_vhdl_allocator_expr(expr).type_mark());
    return nullary_exprt{
      ID_vhdl_allocator,
      vhdl_access_typet{irep_idt{}, std::move(designated_type)}};
  }
  else if(expr.id() == ID_all)
  {
    // IEEE 1076-2008 8.3: the object designated by an access value
    auto prefix = typecheck_expr(to_vhdl_all_expr(expr).prefix());
    if(prefix.type().id() != ID_vhdl_access)
      throw errort{}.with_location(expr.source_location())
        << ".all requires an access value, got "
        << vhdl_type_to_string(prefix.type());
    auto designated_type = to_vhdl_access_type(prefix.type()).designated_type();
    return unary_exprt{ID_dereference, std::move(prefix), designated_type};
  }
  else if(expr.id() == ID_vhdl_aggregate)
  {
    // typed in convert_to
    expr.type() = typet{ID_vhdl_aggregate};
    return expr;
  }
  else if(expr.id() == ID_vhdl_indexed)
  {
    return typecheck_indexed(std::move(expr));
  }
  else if(expr.id() == ID_vhdl_slice)
  {
    return typecheck_slice(std::move(expr));
  }
  else if(expr.id() == ID_vhdl_attribute)
  {
    return typecheck_attribute(std::move(expr));
  }
  else if(expr.id() == ID_vhdl_qualified)
  {
    auto &qualified = to_vhdl_qualified_expr(expr);
    auto type = typecheck_type_mark(qualified.type_mark());
    return convert_to(typecheck_expr(qualified.op()), type);
  }
  else if(expr.id() == ID_member)
  {
    auto &member_expr = to_member_expr(expr);
    auto prefix = typecheck_expr(member_expr.compound());
    irep_idt component_name = to_lower(member_expr.get_component_name());

    // IEEE 1076-2008 8.3: implicit dereference of an access value
    if(prefix.type().id() == ID_vhdl_access)
    {
      auto designated_type =
        to_vhdl_access_type(prefix.type()).designated_type();
      prefix = unary_exprt{ID_dereference, std::move(prefix), designated_type};
    }

    if(prefix.type().id() != ID_vhdl_record)
      throw errort{}.with_location(expr.source_location())
        << "selected name requires a record, got "
        << vhdl_type_to_string(prefix.type());

    auto &record_type = to_vhdl_record_type(prefix.type());

    if(!record_type.has_component(component_name))
      throw errort{}.with_location(expr.source_location())
        << "the record has no element `" << component_name << "'";

    auto &component = record_type.get_component(component_name);
    return vhdl_member_exprt{
      std::move(prefix), component_name, component.type()};
  }
  else if(
    expr.id() == ID_and || expr.id() == ID_or || expr.id() == ID_nand ||
    expr.id() == ID_nor || expr.id() == ID_xor || expr.id() == ID_xnor ||
    expr.id() == ID_equal || expr.id() == ID_notequal || expr.id() == ID_lt ||
    expr.id() == ID_le || expr.id() == ID_gt || expr.id() == ID_ge ||
    expr.id() == ID_plus || expr.id() == ID_minus || expr.id() == ID_mult ||
    expr.id() == ID_div || expr.id() == ID_mod || expr.id() == ID_vhdl_rem ||
    expr.id() == ID_power || expr.id() == ID_concatenation ||
    expr.id() == ID_shl || expr.id() == ID_lshr || expr.id() == ID_ashr ||
    expr.id() == ID_vhdl_sla || expr.id() == ID_rol || expr.id() == ID_ror)
  {
    return typecheck_binary(std::move(expr));
  }
  else if(
    expr.id() == ID_not || expr.id() == ID_unary_minus ||
    expr.id() == ID_unary_plus || expr.id() == ID_abs ||
    expr.id() == ID_typecast)
  {
    return typecheck_unary(std::move(expr));
  }
  else if(expr.id() == ID_if)
  {
    throw errort{}.with_location(expr.source_location())
      << "conditional expressions are only allowed in assignments";
  }
  else if(expr.id() == ID_range)
  {
    throw errort{}.with_location(expr.source_location()) << "unexpected range";
  }
  else
    throw errort{}.with_location(expr.source_location())
      << "unexpected expression: " << expr.id();
}

exprt vhdl_typecheckt::typecheck_symbol(symbol_exprt symbol_expr)
{
  irep_idt identifier = symbol_expr.get_identifier();
  auto declaration = lookup(to_lower(identifier));

  if(!declaration.has_value())
    throw errort{}.with_location(symbol_expr.source_location())
      << "`" << identifier << "' is not declared";

  exprt result;

  switch(declaration->kind)
  {
  case declarationt::LITERALS:
    // An enumeration literal, possibly overloaded (IEEE 1076-2008
    // 5.2.2.1); the type is then determined by the context, in
    // convert_to.
    if(declaration->literals.size() == 1)
      result = declaration->literals.front();
    else
      result = vhdl_overloaded_literal_exprt{identifier, declaration->literals};
    break;

  case declarationt::CONSTANT:
    // constants are inlined
    result = declaration->value;
    break;

  case declarationt::OBJECT:
  {
    // signals, ports, variables
    auto &symbol = symbol_table.lookup_ref(declaration->symbol);
    result = symbol_exprt{symbol.name, symbol.type};
    break;
  }

  case declarationt::TYPE:
    throw errort{}.with_location(symbol_expr.source_location())
      << "`" << identifier << "' is a type";

  case declarationt::LABEL:
    throw errort{}.with_location(symbol_expr.source_location())
      << "`" << identifier << "' is a label";
  }

  result.add_source_location() = symbol_expr.source_location();
  return result;
}

/// IEEE 1076-2008 8.4: a static index must be in the index range
void vhdl_typecheckt::check_index(
  const exprt &index,
  const vhdl_array_typet &array_type,
  const source_locationt &source_location)
{
  auto value = constant_value(index);
  if(!value.has_value())
    return;

  auto range = array_type.range();
  if(*value < range.low() || *value > range.high())
    throw errort{}.with_location(source_location)
      << "index " << *value << " is outside of the range " << range.to_string()
      << " of " << array_type.name();
}

/// An indexed name, a function call, or a type conversion; these
/// cannot be distinguished syntactically.
exprt vhdl_typecheckt::typecheck_indexed(exprt expr)
{
  auto &indexed = to_vhdl_indexed_expr(expr);
  auto &prefix = indexed.prefix();

  // the arguments are association elements
  exprt::operandst arguments;
  for(std::size_t i = 0; i < indexed.number_of_arguments(); i++)
  {
    auto &association = indexed.argument(i);
    if(association.is_named())
      throw errort{}.with_location(association.source_location())
        << "named association is not supported in calls";
    arguments.push_back(association.actual());
  }

  if(prefix.id() == ID_symbol)
  {
    irep_idt lower_case_name =
      to_lower(to_symbol_expr(prefix).get_identifier());
    auto declaration = lookup(lower_case_name);

    if(declaration.has_value() && declaration->kind == declarationt::TYPE)
    {
      // a type conversion
      if(arguments.size() != 1)
        throw errort{}.with_location(expr.source_location())
          << "type conversion takes one argument";

      return typecheck_type_conversion(
        typecheck_expr(arguments.front()), declaration->type);
    }

    // a function of the IEEE packages? Declarations shadow these.
    if(!declaration.has_value())
    {
      if(!is_known_function(lower_case_name))
        throw errort{}.with_location(prefix.source_location())
          << "`" << to_symbol_expr(prefix).get_identifier()
          << "' is not declared";

      return typecheck_function_call(
        lower_case_name, std::move(arguments), expr.source_location());
    }
  }

  // an indexed name
  auto prefix_typed = typecheck_expr(prefix);

  if(arguments.size() != 1)
    throw errort{}.with_location(expr.source_location())
      << "only one-dimensional arrays are supported";

  auto &argument = arguments.front();

  // the argument may be a range, e.g., v(x'range)
  if(argument.id() == ID_vhdl_attribute)
  {
    auto attribute = to_lower(to_vhdl_attribute_expr(argument).attribute());
    if(attribute == "range" || attribute == "reverse_range")
    {
      vhdl_slice_exprt slice{prefix, argument};
      slice.add_source_location() = expr.source_location();
      return typecheck_slice(std::move(slice));
    }
  }

  auto &prefix_type = prefix_typed.type();

  if(
    prefix_type.id() != ID_vhdl_array ||
    !to_vhdl_array_type(prefix_type).is_constrained())
    throw errort{}.with_location(expr.source_location())
      << "indexing requires an array, got " << vhdl_type_to_string(prefix_type);

  auto &array_type = to_vhdl_array_type(prefix_type);
  auto index = convert_to(typecheck_expr(argument), vhdl_integer_type());
  check_index(index, array_type, expr.source_location());

  // as index_exprt, but with the VHDL types
  return binary_exprt{
    std::move(prefix_typed),
    ID_index,
    std::move(index),
    array_type.element_type()};
}

/// IEEE 1076-2008 8.5: a slice, prefix(range). The result is a
/// vhdl_slice_exprt with a static range, typed with the array subtype
/// of the slice.
exprt vhdl_typecheckt::typecheck_slice(exprt expr)
{
  auto &slice = to_vhdl_slice_expr(expr);
  auto prefix = typecheck_expr(slice.prefix());
  auto range = typecheck_range(slice.range());

  auto &prefix_type = prefix.type();

  if(!is_vhdl_vector_type(prefix_type))
    throw errort{}.with_location(expr.source_location())
      << "slices are only supported on vectors, got "
      << vhdl_type_to_string(prefix_type);

  auto &array_type = to_vhdl_array_type(prefix_type);
  auto prefix_range = array_type.range();

  if(range.direction != prefix_range.direction)
    throw errort{}.with_location(expr.source_location())
      << "the direction of a slice must match the direction of the vector";

  // IEEE 1076-2008 8.5: a null slice is permitted
  if(
    range.length() != 0 &&
    (range.low() < prefix_range.low() || range.high() > prefix_range.high()))
    throw errort{}.with_location(expr.source_location())
      << "the slice " << range.to_string() << " is outside of the range "
      << prefix_range.to_string() << " of " << array_type.name();

  vhdl_range_exprt typed_range{
    vhdl_integer_constant(range.left, vhdl_integer_type()),
    to_irep_id(range.direction),
    vhdl_integer_constant(range.right, vhdl_integer_type())};

  vhdl_slice_exprt result{std::move(prefix), std::move(typed_range)};
  result.type() = vhdl_constrained_array_type(array_type, range);
  result.add_source_location() = expr.source_location();
  return std::move(result);
}

/// IEEE 1076-2008 16.2: predefined attributes
exprt vhdl_typecheckt::typecheck_attribute(exprt expr)
{
  auto &attribute_expr = to_vhdl_attribute_expr(expr);
  auto &prefix = attribute_expr.prefix();
  irep_idt attribute = to_lower(attribute_expr.attribute());

  // the prefix may be a type or an object
  std::optional<typet> type;
  std::optional<exprt> prefix_expr;

  if(prefix.id() == ID_symbol)
    type = lookup_type(to_lower(to_symbol_expr(prefix).get_identifier()));

  if(!type.has_value())
  {
    prefix_expr = typecheck_expr(prefix);
    type = prefix_expr->type();
  }

  auto &prefix_type = *type;

  if(attribute == "event")
  {
    // IEEE 1076-2008 16.2.4: the prefix is a signal
    if(
      !prefix_expr.has_value() || prefix_expr->id() != ID_symbol ||
      ns.lookup(to_symbol_expr(*prefix_expr)).is_auxiliary)
      throw errort{}.with_location(expr.source_location())
        << "'event requires a signal";

    return unary_exprt{ID_vhdl_event, *prefix_expr, vhdl_boolean_type()};
  }
  else if(attribute == "length")
  {
    if(
      prefix_type.id() != ID_vhdl_array ||
      !to_vhdl_array_type(prefix_type).is_constrained())
      throw errort{}.with_location(expr.source_location())
        << "'length requires a constrained array";

    return vhdl_integer_constant(
      to_vhdl_array_type(prefix_type).length(), vhdl_integer_type());
  }
  else if(
    attribute == "left" || attribute == "right" || attribute == "high" ||
    attribute == "low")
  {
    bool first = attribute == "left" || attribute == "low";

    // IEEE 1076-2008 16.2.2 for scalar types, 16.2.3 for arrays
    if(prefix_type.id() == ID_vhdl_enumeration)
    {
      auto &enumeration_type = to_vhdl_enumeration_type(prefix_type);
      auto &elements = enumeration_type.elements();
      return constant_exprt{
        first ? elements.front().id() : elements.back().id(), prefix_type};
    }

    vhdl_ranget range;
    if(prefix_type.id() == ID_vhdl_integer)
      range = to_vhdl_integer_type(prefix_type).range();
    else if(
      prefix_type.id() == ID_vhdl_array &&
      to_vhdl_array_type(prefix_type).is_constrained())
      range = to_vhdl_array_type(prefix_type).range();
    else
      throw errort{}.with_location(expr.source_location())
        << "'" << attribute << " requires a scalar or constrained array type";

    mp_integer value;
    if(attribute == "left")
      value = range.left;
    else if(attribute == "right")
      value = range.right;
    else if(attribute == "high")
      value = range.high();
    else
      value = range.low();

    // the attributes of an array are of the index type, those of a
    // scalar of the scalar type
    if(prefix_type.id() == ID_vhdl_integer)
      return vhdl_integer_constant(value, prefix_type);
    else
      return vhdl_integer_constant(value, vhdl_integer_type());
  }
  else if(attribute == "range" || attribute == "reverse_range")
  {
    throw errort{}.with_location(expr.source_location())
      << "range attribute outside of a range context";
  }
  else
    throw errort{}.with_location(expr.source_location())
      << "unsupported attribute `" << attribute << "'";
}

/// The functions of std_logic_1164, numeric_std, std_logic_arith and
/// std_logic_unsigned that we support, and the package each comes from.
static const std::map<irep_idt, irep_idt> &known_functions()
{
  static const std::map<irep_idt, irep_idt> functions = {
    {"rising_edge", "std_logic_1164"},
    {"falling_edge", "std_logic_1164"},
    {"to_bit", "std_logic_1164"},
    {"to_bitvector", "std_logic_1164"},
    {"to_stdulogic", "std_logic_1164"},
    {"to_stdlogicvector", "std_logic_1164"},
    {"to_stdulogicvector", "std_logic_1164"},
    {"to_integer", "numeric_std"},
    {"to_unsigned", "numeric_std"},
    {"to_signed", "numeric_std"},
    {"resize", "numeric_std"},
    {"shift_left", "numeric_std"},
    {"shift_right", "numeric_std"},
    {"conv_integer", "std_logic_arith"},
    {"conv_unsigned", "std_logic_arith"},
    {"conv_signed", "std_logic_arith"},
    {"conv_std_logic_vector", "std_logic_arith"}};
  return functions;
}

bool vhdl_typecheckt::is_known_function(irep_idt name) const
{
  return known_functions().find(name) != known_functions().end();
}

/// the base type name of an array or enumeration, or empty
static irep_idt base_name_of(const typet &type)
{
  if(
    type.id() == ID_vhdl_array || type.id() == ID_vhdl_enumeration ||
    type.id() == ID_vhdl_integer || type.id() == ID_vhdl_record)
    return static_cast<const vhdl_typet &>(type).base_name();
  else
    return irep_idt{};
}

exprt vhdl_typecheckt::typecheck_function_call(
  irep_idt name,
  exprt::operandst arguments,
  const source_locationt &source_location)
{
  auto f_it = known_functions().find(name);
  PRECONDITION(f_it != known_functions().end());

  // The function must be visible, through a use clause of its package.
  // conv_integer is in both std_logic_arith and std_logic_unsigned.
  auto package = f_it->second;
  if(
    !uses_package(package) &&
    !(package == "std_logic_arith" &&
      (uses_package("std_logic_unsigned") || uses_package("std_logic_signed"))))
    throw errort{}.with_location(source_location)
      << "`" << name << "' is not declared; it is in package " << package;

  auto expect_arguments = [&](std::size_t n)
  {
    if(arguments.size() != n)
      throw errort{}.with_location(source_location)
        << "function `" << name << "' expects " << n << " argument(s)";
  };

  auto base_name_of_arg = [](const exprt &e) { return base_name_of(e.type()); };

  if(name == "rising_edge" || name == "falling_edge")
  {
    expect_arguments(1);
    auto signal = typecheck_expr(arguments[0]);

    if(
      signal.id() != ID_symbol || !is_vhdl_scalar_bit_type(signal.type()) ||
      ns.lookup(to_symbol_expr(signal)).is_auxiliary)
      throw errort{}.with_location(source_location)
        << name << " requires a signal of type std_ulogic or bit";

    return unary_exprt{
      name == "rising_edge" ? ID_vhdl_rising_edge : ID_vhdl_falling_edge,
      std::move(signal),
      vhdl_boolean_type()};
  }
  else if(name == "to_bit" || name == "to_stdulogic")
  {
    // std_logic_1164: to_bit(std_ulogic), to_stdulogic(bit)
    expect_arguments(1);
    auto value = typecheck_expr(arguments[0]);
    irep_idt expected = name == "to_bit" ? "std_ulogic" : "bit";

    if(
      !is_vhdl_scalar_bit_type(value.type()) ||
      base_name_of_arg(value) != expected)
      throw errort{}.with_location(source_location)
        << name << " requires an argument of type " << expected;

    typet result_type =
      name == "to_bit" ? vhdl_bit_type() : vhdl_std_ulogic_type();
    return typecast_exprt{std::move(value), result_type};
  }
  else if(
    name == "to_bitvector" || name == "to_stdlogicvector" ||
    name == "to_stdulogicvector")
  {
    // std_logic_1164: between bit_vector and std_(u)logic_vector
    expect_arguments(1);
    auto value = typecheck_expr(arguments[0]);

    if(!is_vhdl_vector_type(value.type()))
      throw errort{}.with_location(source_location)
        << name << " requires a vector";

    bool from_bit = base_name_of_arg(value) == "bit_vector";
    bool to_bit = name == "to_bitvector";

    if(from_bit == to_bit)
      throw errort{}.with_location(source_location)
        << name << " requires an argument of type "
        << (to_bit ? "std_ulogic_vector" : "bit_vector");

    auto range = to_vhdl_array_type(value.type()).range();
    irep_idt result_name = to_bit                        ? "bit_vector"
                           : name == "to_stdlogicvector" ? "std_logic_vector"
                                                         : "std_ulogic_vector";
    return typecast_exprt{
      std::move(value), vhdl_vector_type(result_name, range)};
  }
  else if(name == "to_integer")
  {
    // numeric_std: to_integer(unsigned), to_integer(signed)
    expect_arguments(1);
    auto vector = typecheck_expr(arguments[0]);

    if(!is_vhdl_numeric_vector_type(vector.type()))
      throw errort{}.with_location(source_location)
        << "to_integer requires an unsigned or signed argument";

    return typecast_exprt{std::move(vector), vhdl_integer_type()};
  }
  else if(name == "conv_integer")
  {
    // std_logic_arith: conv_integer(integer | unsigned | signed | std_ulogic);
    // std_logic_unsigned/std_logic_signed: conv_integer(std_logic_vector)
    expect_arguments(1);
    auto value = typecheck_expr(arguments[0]);
    auto base = base_name_of_arg(value);

    if(is_vhdl_integer_type(value.type()))
      return value;

    if(is_vhdl_numeric_vector_type(value.type()))
      return typecast_exprt{std::move(value), vhdl_integer_type()};

    if(
      base == "std_ulogic_vector" &&
      (uses_package("std_logic_unsigned") || uses_package("std_logic_signed")))
    {
      // std_logic_signed interprets std_logic_vector as signed
      bool is_signed =
        uses_package("std_logic_signed") && !uses_package("std_logic_unsigned");
      auto range = to_vhdl_array_type(value.type()).range();
      exprt numeric = typecast_exprt{
        std::move(value),
        vhdl_vector_type(is_signed ? "signed" : "unsigned", range)};
      return typecast_exprt{std::move(numeric), vhdl_integer_type()};
    }

    throw errort{}.with_location(source_location)
      << "conv_integer is not defined for "
      << vhdl_type_to_string(value.type());
  }
  else if(name == "to_unsigned" || name == "to_signed")
  {
    // numeric_std: to_unsigned(natural, natural), to_signed(integer, natural)
    expect_arguments(2);
    auto value = typecheck_expr(arguments[0]);
    auto width = typecheck_static_integer(arguments[1]);

    if(width <= 0)
      throw errort{}.with_location(source_location) << "width must be positive";

    if(is_vhdl_universal_type(value.type()))
      value = convert_to(std::move(value), vhdl_integer_type());

    if(!is_vhdl_integer_type(value.type()))
      throw errort{}.with_location(source_location)
        << name << " requires an integer argument";

    vhdl_ranget range{width - 1, 0, vhdl_directiont::DOWNTO};
    return typecast_exprt{
      std::move(value),
      vhdl_vector_type(name == "to_signed" ? "signed" : "unsigned", range)};
  }
  else if(
    name == "conv_std_logic_vector" || name == "conv_unsigned" ||
    name == "conv_signed")
  {
    // std_logic_arith: from integer, unsigned, signed or std_ulogic
    expect_arguments(2);
    auto value = typecheck_expr(arguments[0]);
    auto width = typecheck_static_integer(arguments[1]);

    if(width <= 0)
      throw errort{}.with_location(source_location) << "width must be positive";

    if(is_vhdl_universal_type(value.type()))
      value = convert_to(std::move(value), vhdl_integer_type());

    if(
      !is_vhdl_integer_type(value.type()) &&
      !is_vhdl_numeric_vector_type(value.type()))
      throw errort{}.with_location(source_location)
        << name << " requires an integer, unsigned or signed argument";

    vhdl_ranget range{width - 1, 0, vhdl_directiont::DOWNTO};
    irep_idt result_name = name == "conv_signed" ? "signed"
                           : name == "conv_std_logic_vector"
                             ? "std_logic_vector"
                             : "unsigned";

    // the conversion goes through the numeric type
    if(
      is_vhdl_numeric_vector_type(value.type()) &&
      !is_vhdl_integer_type(value.type()))
      value = typecast_exprt{std::move(value), vhdl_integer_type()};

    if(result_name == "std_logic_vector")
    {
      exprt numeric =
        typecast_exprt{std::move(value), vhdl_vector_type("unsigned", range)};
      return typecast_exprt{
        std::move(numeric), vhdl_vector_type(result_name, range)};
    }

    return typecast_exprt{
      std::move(value), vhdl_vector_type(result_name, range)};
  }
  else if(name == "resize")
  {
    // numeric_std: resize(unsigned | signed, natural)
    expect_arguments(2);
    auto value = typecheck_expr(arguments[0]);
    auto width = typecheck_static_integer(arguments[1]);

    if(!is_vhdl_numeric_vector_type(value.type()))
      throw errort{}.with_location(source_location)
        << "resize requires an unsigned or signed argument";

    if(width <= 0)
      throw errort{}.with_location(source_location) << "width must be positive";

    auto &value_type = to_vhdl_array_type(value.type());
    bool is_signed = value_type.base_name() == "signed";
    vhdl_ranget range{width - 1, 0, vhdl_directiont::DOWNTO};
    auto result_type =
      vhdl_vector_type(is_signed ? "signed" : "unsigned", range);

    auto old_range = value_type.range();

    if(is_signed && width < old_range.length())
    {
      // numeric_std keeps the sign bit and the rightmost width-1 bits:
      // s(s'left) & s(low + width - 2 downto low)
      exprt sign_bit = binary_exprt{
        value,
        ID_index,
        vhdl_integer_constant(old_range.left, vhdl_integer_type()),
        value_type.element_type()};

      if(width == 1)
      {
        vhdl_array_typet one_bit_type{
          result_type.base_name(),
          value_type.element_type(),
          vhdl_ranget{0, 0, vhdl_directiont::DOWNTO}};
        return typecast_exprt{
          concatenation_exprt{{std::move(sign_bit)}, one_bit_type},
          result_type};
      }

      vhdl_ranget low_range{
        old_range.low() + width - 2, old_range.low(), vhdl_directiont::DOWNTO};
      vhdl_range_exprt low_range_expr{
        vhdl_integer_constant(low_range.left, vhdl_integer_type()),
        ID_vhdl_downto,
        vhdl_integer_constant(low_range.right, vhdl_integer_type())};
      vhdl_slice_exprt low_bits{value, std::move(low_range_expr)};
      low_bits.type() = vhdl_constrained_array_type(value_type, low_range);

      return concatenation_exprt{
        std::move(sign_bit), std::move(low_bits), result_type};
    }

    return typecast_exprt{std::move(value), result_type};
  }
  else if(name == "shift_left" || name == "shift_right")
  {
    // numeric_std: shift_left(unsigned | signed, natural)
    expect_arguments(2);
    auto value = typecheck_expr(arguments[0]);
    auto amount = convert_to(typecheck_expr(arguments[1]), vhdl_integer_type());

    if(!is_vhdl_numeric_vector_type(value.type()))
      throw errort{}.with_location(source_location)
        << name << " requires an unsigned or signed argument";

    auto type = value.type();
    bool is_signed = base_name_of(type) == "signed";

    irep_idt id = name == "shift_left" ? ID_shl : is_signed ? ID_ashr : ID_lshr;
    return binary_exprt{std::move(value), id, std::move(amount), type};
  }
  else
    UNREACHABLE;
}

/// IEEE 1076-2008 9.3.6: array types are closely related if they have
/// the same dimensionality and closely related element types; std_logic
/// and std_ulogic are the same type, and bit is a different type
static bool closely_related_vectors(const typet &a, const typet &b)
{
  auto a_bit = base_name_of(a) == "bit_vector";
  auto b_bit = base_name_of(b) == "bit_vector";
  return a_bit == b_bit;
}

/// IEEE 1076-2008 9.3.6: type conversion
exprt vhdl_typecheckt::typecheck_type_conversion(exprt expr, const typet &type)
{
  if(is_vhdl_universal_type(expr.type()))
    return convert_to(std::move(expr), type);

  auto &source_type = expr.type();

  if(type.id() == ID_vhdl_array)
  {
    auto &target_type = to_vhdl_array_type(type);

    if(
      !is_vhdl_vector_type(source_type) ||
      !closely_related_vectors(source_type, type))
      throw errort{}.with_location(expr.source_location())
        << "conversion to " << vhdl_type_to_string(type)
        << " requires a closely related array type, got "
        << vhdl_type_to_string(source_type);

    auto source_range = to_vhdl_array_type(source_type).range();

    // e.g., std_logic_vector(u); the range is that of the operand
    if(!target_type.is_constrained())
      return typecast_exprt{
        std::move(expr),
        vhdl_constrained_array_type(target_type, source_range)};

    if(target_type.length() != source_range.length())
      throw errort{}.with_location(expr.source_location())
        << "conversion to " << vhdl_type_to_string(type)
        << " requires an array of the same length, got "
        << vhdl_type_to_string(source_type);

    return typecast_exprt{std::move(expr), type};
  }
  else if(is_vhdl_integer_type(type))
  {
    if(!is_vhdl_integer_type(source_type))
      throw errort{}.with_location(expr.source_location())
        << "conversion to integer requires an integer";

    return typecast_exprt{std::move(expr), type};
  }
  else if(is_vhdl_scalar_bit_type(type))
  {
    // bit and std_ulogic are not closely related; use to_bit/to_stdulogic
    if(!vhdl_types_compatible(source_type, type))
      throw errort{}.with_location(expr.source_location())
        << "conversion to " << vhdl_type_to_string(type) << " from "
        << vhdl_type_to_string(source_type) << " is not a type conversion";

    expr.type() = type;
    return expr;
  }
  else
    throw errort{}.with_location(expr.source_location())
      << "unsupported type conversion";
}

/// The digits of a bit string literal (IEEE 1076-2008 15.8), as the
/// characters of the element literals, most significant first
static std::optional<std::string> bit_string_digits(const std::string &literal)
{
  std::string result;
  std::size_t i = 0;

  // optional length is not supported
  if(i < literal.size() && isdigit(literal[i]))
    return {};

  // optional signedness
  if(
    i < literal.size() && (literal[i] == 'u' || literal[i] == 'U' ||
                           literal[i] == 's' || literal[i] == 'S'))
    i++;

  if(i >= literal.size())
    return {};

  char base_char = tolower(literal[i]);
  i++;

  unsigned bits_per_digit;
  if(base_char == 'b')
    bits_per_digit = 1;
  else if(base_char == 'o')
    bits_per_digit = 3;
  else if(base_char == 'x')
    bits_per_digit = 4;
  else
    return {};

  // skip the opening quote
  if(i >= literal.size() || literal[i] != '"')
    return {};
  i++;

  for(; i < literal.size() && literal[i] != '"'; i++)
  {
    char ch = literal[i];
    if(ch == '_')
      continue;

    unsigned value;
    if(isdigit(ch))
      value = ch - '0';
    else if(isxdigit(ch))
      value = tolower(ch) - 'a' + 10;
    else
      return {}; // other element literals in bit strings are not supported

    if(value >= (1u << bits_per_digit))
      return {};

    for(unsigned b = bits_per_digit; b > 0; b--)
      result.push_back((value >> (b - 1)) & 1 ? '1' : '0');
  }

  return result;
}

/// an array value from element literals, e.g., a string literal
exprt vhdl_typecheckt::array_from_literals(
  const std::string &literals,
  const vhdl_array_typet &type,
  const source_locationt &source_location)
{
  auto &element_type = type.element_type();

  if(element_type.id() != ID_vhdl_enumeration)
    throw errort{}.with_location(source_location)
      << "string literal where " << vhdl_type_to_string(type) << " is expected";

  auto &enumeration_type = to_vhdl_enumeration_type(element_type);

  // an array value, as array_exprt but with the VHDL type
  multi_ary_exprt result{ID_array, {}, type};
  result.operands().reserve(literals.size());

  for(char ch : literals)
  {
    auto literal = vhdl_enumeration_typet::character_literal(ch);
    if(!enumeration_type.position(literal).has_value())
      throw errort{}.with_location(source_location)
        << "'" << ch << "' is not a value of " << enumeration_type.name();
    result.operands().push_back(constant_exprt{literal, element_type});
  }

  result.add_source_location() = source_location;
  return std::move(result);
}

/// IEEE 1076-2008 9.3.3.3: the elements of an array aggregate, from
/// the low index. The associations are either all positional or all
/// named; an others choice may follow either. Each element is given
/// exactly once.
std::vector<exprt> vhdl_typecheckt::aggregate_elements(
  const vhdl_aggregate_exprt &aggregate,
  const vhdl_array_typet &type)
{
  auto range = type.range();
  auto size = numeric_cast_v<std::size_t>(range.length());
  auto &associations = aggregate.operands();
  auto &element_type = type.element_type();

  std::vector<std::optional<exprt>> elements(size);
  std::optional<exprt> others;
  std::size_t positional = 0;
  bool named = false;

  auto set_element = [&](
                       const mp_integer &index,
                       const exprt &value,
                       const source_locationt &source_location)
  {
    if(index < range.low() || index > range.high())
      throw errort{}.with_location(source_location)
        << "the index " << index << " is outside of the range of "
        << vhdl_type_to_string(type);

    auto &element = elements[numeric_cast_v<std::size_t>(index - range.low())];

    if(element.has_value())
      throw errort{}.with_location(source_location)
        << "element " << index << " is given more than once";

    element = value;
  };

  for(std::size_t i = 0; i < associations.size(); i++)
  {
    auto &association = aggregate.association(i);
    auto &source_location = association.source_location();
    auto value = convert_to(typecheck_expr(association.value()), element_type);

    if(association.is_positional())
    {
      if(named)
        throw errort{}.with_location(source_location)
          << "positional association after named association";

      if(positional >= size)
        throw errort{}.with_location(source_location)
          << "too many elements in aggregate; " << vhdl_type_to_string(type)
          << " has " << size;

      mp_integer index = range.direction == vhdl_directiont::TO
                           ? range.left + positional
                           : range.left - positional;
      set_element(index, value, source_location);
      positional++;
    }
    else
    {
      for(auto &choice_irep : association.choices())
      {
        auto &choice = static_cast<const exprt &>(choice_irep);

        if(choice.id() == ID_vhdl_others)
        {
          // the only choice of the last association
          if(i + 1 != associations.size() || association.choices().size() != 1)
            throw errort{}.with_location(choice.source_location())
              << "others must be the last choice";

          others = value;
        }
        else
        {
          if(positional != 0)
            throw errort{}.with_location(source_location)
              << "named association after positional association";

          named = true;

          if(choice.id() == ID_range)
          {
            auto choice_range = typecheck_range(choice);
            for(mp_integer index = choice_range.low();
                index <= choice_range.high();
                ++index)
              set_element(index, value, choice.source_location());
          }
          else
            set_element(
              typecheck_static_integer(choice),
              value,
              choice.source_location());
        }
      }
    }
  }

  std::vector<exprt> result;
  result.reserve(size);

  for(std::size_t i = 0; i < size; i++)
  {
    if(elements[i].has_value())
      result.push_back(std::move(*elements[i]));
    else if(others.has_value())
      result.push_back(*others);
    else
      throw errort{}.with_location(aggregate.source_location())
        << "aggregate gives no value for element " << range.low() + i << " of "
        << vhdl_type_to_string(type);
  }

  return result;
}

/// IEEE 1076-2008 9.3.3: aggregates. Array aggregates become
/// array_exprt, with the elements from left to right, or array_of_exprt
/// when there is only an others choice; record aggregates become
/// struct_exprt.
exprt vhdl_typecheckt::typecheck_aggregate(exprt expr, const typet &type)
{
  auto &aggregate = to_vhdl_aggregate_expr(expr);

  if(type.id() == ID_vhdl_array)
  {
    auto &array_type = to_vhdl_array_type(type);

    if(!array_type.is_constrained())
      throw errort{}.with_location(aggregate.source_location())
        << "aggregate requires a constrained array type, got "
        << vhdl_type_to_string(type);

    // only others?
    if(
      aggregate.operands().size() == 1 &&
      !aggregate.association(0).is_positional() &&
      static_cast<const exprt &>(aggregate.association(0).choices().front())
          .id() == ID_vhdl_others)
    {
      auto value = convert_to(
        typecheck_expr(aggregate.association(0).value()),
        array_type.element_type());
      unary_exprt result{ID_array_of, std::move(value), array_type};
      result.add_source_location() = aggregate.source_location();
      return std::move(result);
    }

    auto elements = aggregate_elements(aggregate, array_type);
    auto range = array_type.range();

    // the elements, from left to right
    exprt::operandst operands;
    operands.reserve(elements.size());

    if(range.direction == vhdl_directiont::TO)
      for(auto &element : elements)
        operands.push_back(std::move(element));
    else
      for(auto it = elements.rbegin(); it != elements.rend(); it++)
        operands.push_back(std::move(*it));

    multi_ary_exprt result{ID_array, std::move(operands), array_type};
    result.add_source_location() = aggregate.source_location();
    return std::move(result);
  }
  else if(type.id() == ID_vhdl_record)
  {
    auto &record_type = to_vhdl_record_type(type);
    auto &components = record_type.components();
    auto &associations = aggregate.operands();

    std::vector<std::optional<exprt>> elements(components.size());
    std::size_t positional = 0;
    bool named = false;

    auto set_element = [&](
                         std::size_t index,
                         const exprt &value,
                         const source_locationt &source_location)
    {
      if(elements[index].has_value())
        throw errort{}.with_location(source_location)
          << "element `" << components[index].get_name()
          << "' is given more than once";

      elements[index] =
        convert_to(typecheck_expr(value), components[index].type());
    };

    for(std::size_t i = 0; i < associations.size(); i++)
    {
      auto &association = aggregate.association(i);
      auto &source_location = association.source_location();
      auto &value = association.value();

      if(association.is_positional())
      {
        if(named)
          throw errort{}.with_location(source_location)
            << "positional association after named association";

        if(positional >= components.size())
          throw errort{}.with_location(source_location)
            << "too many elements in aggregate; the record has "
            << components.size();

        set_element(positional, value, source_location);
        positional++;
      }
      else
      {
        for(auto &choice_irep : association.choices())
        {
          auto &choice = static_cast<const exprt &>(choice_irep);

          if(choice.id() == ID_vhdl_others)
          {
            if(
              i + 1 != associations.size() || association.choices().size() != 1)
              throw errort{}.with_location(choice.source_location())
                << "others must be the last choice";

            for(std::size_t c = 0; c < components.size(); c++)
              if(!elements[c].has_value())
                set_element(c, value, source_location);
          }
          else if(choice.id() == ID_symbol)
          {
            if(positional != 0)
              throw errort{}.with_location(source_location)
                << "named association after positional association";

            named = true;

            auto name = to_lower(to_symbol_expr(choice).get_identifier());
            bool found = false;

            for(std::size_t c = 0; c < components.size(); c++)
              if(components[c].get_name() == name)
              {
                set_element(c, value, choice.source_location());
                found = true;
              }

            if(!found)
              throw errort{}.with_location(choice.source_location())
                << "the record has no element `" << name << "'";
          }
          else
            throw errort{}.with_location(choice.source_location())
              << "unexpected choice in record aggregate";
        }
      }
    }

    exprt::operandst element_operands;
    for(std::size_t i = 0; i < components.size(); i++)
    {
      if(!elements[i].has_value())
        throw errort{}.with_location(aggregate.source_location())
          << "aggregate gives no value for element `"
          << components[i].get_name() << "'";
      element_operands.push_back(std::move(*elements[i]));
    }

    struct_exprt result{std::move(element_operands), type};
    result.add_source_location() = aggregate.source_location();
    return std::move(result);
  }
  else
    throw errort{}.with_location(aggregate.source_location())
      << "aggregate requires an array or record type, got "
      << vhdl_type_to_string(type);
}

/// IEEE 1076-2008 15.5.1, 16.3: a physical literal of type time, e.g.
/// 10 ns or 1.5 us; the value is in femtoseconds
exprt vhdl_typecheckt::typecheck_physical_literal(
  const vhdl_physical_literal_exprt &literal)
{
  static const std::map<irep_idt, mp_integer> units = {
    {"fs", 1},
    {"ps", 1000},
    {"ns", 1000000},
    {"us", 1000000000},
    {"ms", mp_integer{1000000000} * 1000},
    {"sec", mp_integer{1000000000} * 1000000},
    {"min", mp_integer{1000000000} * 60000000},
    {"hr", mp_integer{1000000000} * 3600000000}};

  auto unit = to_lower(literal.unit());
  auto u_it = units.find(unit);
  if(u_it == units.end())
    throw errort{}.with_location(literal.source_location())
      << "unknown unit `" << literal.unit() << "'";

  // decimal literal, possibly with a fractional part
  std::string value_string = id2string(literal.value());
  value_string.erase(
    std::remove(value_string.begin(), value_string.end(), '_'),
    value_string.end());

  auto dot = value_string.find('.');
  if(value_string.find_first_of("eE#") != std::string::npos)
    throw errort{}.with_location(literal.source_location())
      << "unsupported physical literal";

  mp_integer value;
  if(dot == std::string::npos)
    value = string2integer(value_string) * u_it->second;
  else
  {
    auto integer_part = string2integer(value_string.substr(0, dot));
    auto fraction = value_string.substr(dot + 1);
    value = integer_part * u_it->second;
    mp_integer scale = u_it->second;
    for(char digit : fraction)
    {
      scale /= 10;
      value += (digit - '0') * scale;
    }
  }

  constant_exprt result{integer2string(value), vhdl_time_type()};
  result.add_source_location() = literal.source_location();
  return std::move(result);
}

/// IEEE 1076-2008 9.2.7: the operators on physical types
exprt vhdl_typecheckt::typecheck_physical_binary(
  irep_idt id,
  exprt lhs,
  exprt rhs,
  const source_locationt &source_location)
{
  bool relational = id == ID_equal || id == ID_notequal || id == ID_lt ||
                    id == ID_le || id == ID_gt || id == ID_ge;

  if(relational || id == ID_plus || id == ID_minus)
  {
    match_types(lhs, rhs);
    auto type =
      relational ? static_cast<typet>(vhdl_boolean_type()) : lhs.type();
    exprt result = binary_exprt{std::move(lhs), id, std::move(rhs), type};
    result.add_source_location() = source_location;
    return result;
  }
  else if(id == ID_mult || id == ID_div)
  {
    // time * integer, integer * time, time / integer; time / time is
    // an integer
    bool lhs_physical = lhs.type().id() == ID_vhdl_physical_type;
    bool rhs_physical = rhs.type().id() == ID_vhdl_physical_type;

    if(lhs_physical && rhs_physical && id == ID_div)
    {
      match_types(lhs, rhs);
      exprt result =
        binary_exprt{std::move(lhs), id, std::move(rhs), vhdl_integer_type()};
      result.add_source_location() = source_location;
      return result;
    }

    if(lhs_physical && rhs_physical)
      throw errort{}.with_location(source_location)
        << "cannot multiply two values of type time";

    auto &integer_operand = lhs_physical ? rhs : lhs;
    integer_operand =
      convert_to(std::move(integer_operand), vhdl_integer_type());

    if(id == ID_div && !lhs_physical)
      throw errort{}.with_location(source_location)
        << "cannot divide an integer by a time";

    exprt result =
      binary_exprt{std::move(lhs), id, std::move(rhs), vhdl_time_type()};
    result.add_source_location() = source_location;
    return result;
  }
  else
    throw errort{}.with_location(source_location)
      << "operator " << id << " is not defined on time";
}

/// IEEE 1076-2008 15.5.2: the value of a decimal or based integer
/// literal
mp_integer vhdl_typecheckt::integer_literal_value(const constant_exprt &expr)
{
  PRECONDITION(expr.type().id() == ID_natural);
  std::string value_string = id2string(expr.get_value());

  // remove underscores
  value_string.erase(
    std::remove(value_string.begin(), value_string.end(), '_'),
    value_string.end());

  auto hash = value_string.find('#');
  if(hash != std::string::npos)
  {
    // based literal: base#digits#
    auto base = string2integer(value_string.substr(0, hash));
    auto last_hash = value_string.rfind('#');
    auto digits = value_string.substr(hash + 1, last_hash - hash - 1);
    if(digits.find('.') != std::string::npos)
      throw errort{}.with_location(expr.source_location())
        << "based real literals are not supported";
    if(last_hash + 1 < value_string.size())
      throw errort{}.with_location(expr.source_location())
        << "exponents on based literals are not supported";
    return string2integer(digits, numeric_cast_v<unsigned>(base));
  }
  else
  {
    auto e = value_string.find_first_of("eE");
    if(e != std::string::npos)
    {
      auto mantissa = string2integer(value_string.substr(0, e));
      auto exponent = string2integer(value_string.substr(e + 1));
      // integer is 32 bits; anything beyond is out of range anyway
      if(exponent > 40)
        throw errort{}.with_location(expr.source_location())
          << "the value " << value_string
          << " is outside of the range of integer";
      return mantissa * power(10, exponent);
    }
    else
      return string2integer(value_string);
  }
}

/// IEEE 1076-2008 9.3.2: the type of a literal that has no typed
/// context, e.g., when both operands of an operator are literals. This
/// is ambiguous in VHDL when both bit and std_logic are visible; we use
/// integer, std_logic and std_logic_vector.
exprt vhdl_typecheckt::literal_with_default_type(exprt literal)
{
  auto id = literal.type().id();

  if(id == ID_natural)
    return convert_to(std::move(literal), vhdl_integer_type());
  else if(id == ID_nullptr)
    throw errort{}.with_location(literal.source_location())
      << "cannot determine the type of null";
  else if(id == ID_char)
    return convert_to(std::move(literal), vhdl_std_logic_type());
  else if(id == ID_string || id == ID_vhdl_bit_string)
    return convert_to(
      std::move(literal), vhdl_unconstrained_array_type("std_logic_vector"));
  else
    throw errort{}.with_location(literal.source_location())
      << "cannot determine the type of the literal";
}

/// IEEE 1076-2008 5.2.1: a static value must be in the range of the
/// subtype
void vhdl_typecheckt::check_range(
  const exprt &expr,
  const vhdl_integer_typet &type,
  const source_locationt &source_location)
{
  auto value = constant_value(expr);
  if(!value.has_value())
    return;

  auto range = type.range();
  if(*value < range.low() || *value > range.high())
    throw errort{}.with_location(source_location)
      << "the value " << *value << " is outside of the range "
      << range.to_string() << " of " << type.name();
}

/// Implicit conversion of a universal literal to the given type, and
/// type matching for typed expressions.
exprt vhdl_typecheckt::convert_to(exprt expr, const typet &type)
{
  auto &source_type = expr.type();
  auto &source_location = expr.source_location();

  if(vhdl_types_compatible(source_type, type))
  {
    // The subtypes may differ. An integer value takes the target
    // subtype, after a range check. An array value keeps its own index
    // range (IEEE 1076-2008 10.5.2.2: the elements correspond by
    // position, the ranges may differ), which the lowering of slices
    // and indexed names relies on; only the lengths must agree.
    if(type.id() == ID_vhdl_array)
    {
      auto &target_type = to_vhdl_array_type(type);
      auto &source_array_type = to_vhdl_array_type(source_type);

      if(!target_type.is_constrained() || source_array_type.is_constrained())
      {
        if(
          target_type.is_constrained() &&
          target_type.length() != source_array_type.length())
          throw errort{}.with_location(source_location)
            << "type mismatch: expected " << vhdl_type_to_string(type)
            << ", got " << vhdl_type_to_string(source_type);

        return expr;
      }
    }

    if(is_vhdl_integer_type(type))
      check_range(expr, to_vhdl_integer_type(type), source_location);

    expr.type() = type;
    return expr;
  }

  if(source_type.id() == ID_natural)
  {
    auto value = integer_literal_value(to_constant_expr(expr));

    if(is_vhdl_integer_type(type))
    {
      auto &integer_type = to_vhdl_integer_type(type);
      auto range = integer_type.range();

      if(value < range.low() || value > range.high())
        throw errort{}.with_location(source_location)
          << "the value " << value << " is outside of the range "
          << range.to_string() << " of " << integer_type.name();

      auto result = vhdl_integer_constant(value, type);
      result.add_source_location() = source_location;
      return std::move(result);
    }
    else
      throw errort{}.with_location(source_location)
        << "integer literal where " << vhdl_type_to_string(type)
        << " is expected";
  }
  else if(source_type.id() == ID_char)
  {
    std::string value = id2string(to_constant_expr(expr).get_value());
    DATA_INVARIANT(value.size() == 1, "character literals have one character");

    if(type.id() == ID_vhdl_enumeration)
    {
      // IEEE 1076-2008 15.6: character literals are case sensitive
      auto &enumeration_type = to_vhdl_enumeration_type(type);
      auto literal = vhdl_enumeration_typet::character_literal(value[0]);
      if(!enumeration_type.position(literal).has_value())
        throw errort{}.with_location(source_location)
          << literal << " is not a value of " << enumeration_type.name();

      constant_exprt result{literal, type};
      result.add_source_location() = source_location;
      return std::move(result);
    }
    else
      throw errort{}.with_location(source_location)
        << "character literal where " << vhdl_type_to_string(type)
        << " is expected";
  }
  else if(
    source_type.id() == ID_string || source_type.id() == ID_vhdl_bit_string)
  {
    if(type.id() != ID_vhdl_array)
      throw errort{}.with_location(source_location)
        << (source_type.id() == ID_string ? "string" : "bit string")
        << " literal where " << vhdl_type_to_string(type) << " is expected";

    auto &array_type = to_vhdl_array_type(type);

    // the element literals
    std::string literals;

    if(source_type.id() == ID_string)
      literals = id2string(to_constant_expr(expr).get_value());
    else
    {
      auto digits =
        bit_string_digits(id2string(to_constant_expr(expr).get_value()));
      if(!digits.has_value())
        throw errort{}.with_location(source_location)
          << "unsupported bit string literal";
      literals = std::move(*digits);
    }

    // IEEE 1076-2008 9.3.2, 9.3.5: for an unconstrained type, e.g.
    // unsigned'("0011") or a constant without a constraint, the literal
    // determines the length; the index range starts at the left bound
    // of the index subtype and has its direction, e.g., 0 to N-1 for
    // bit_vector, whose index subtype is natural
    if(!array_type.is_constrained())
    {
      auto range = array_type.range_for_length(literals.size());
      return array_from_literals(
        literals,
        vhdl_constrained_array_type(array_type, range),
        source_location);
    }

    // IEEE 1076-2008 15.8: without an explicit length, a bit string
    // literal has exactly the number of bits of its digits; string
    // literals have the number of characters. Both must match the type.
    if(mp_integer(literals.size()) != array_type.length())
      throw errort{}.with_location(source_location)
        << (source_type.id() == ID_string ? "string" : "bit string")
        << " literal has " << literals.size() << " elements, but "
        << vhdl_type_to_string(type) << " has " << array_type.length();

    return array_from_literals(literals, array_type, source_location);
  }
  else if(source_type.id() == ID_vhdl_aggregate)
  {
    return typecheck_aggregate(std::move(expr), type);
  }
  else if(source_type.id() == ID_nullptr)
  {
    // IEEE 1076-2008 5.4.1: null is a value of every access type
    if(type.id() != ID_vhdl_access)
      throw errort{}.with_location(source_location)
        << "null where " << vhdl_type_to_string(type) << " is expected";
    constant_exprt result{"null", type};
    result.add_source_location() = source_location;
    return std::move(result);
  }
  else if(source_type.id() == ID_real)
  {
    throw errort{}.with_location(source_location)
      << "real literals are not supported";
  }
  else if(source_type.id() == ID_vhdl_overloaded_literal)
  {
    // IEEE 1076-2008 5.2.2.1: pick the literal of the expected type
    for(auto &candidate : to_vhdl_overloaded_literal_expr(expr).candidates())
      if(vhdl_types_compatible(candidate.type(), type))
      {
        exprt result = candidate;
        result.type() = type;
        result.add_source_location() = source_location;
        return result;
      }

    throw errort{}.with_location(source_location)
      << "`" << to_vhdl_overloaded_literal_expr(expr).identifier()
      << "' is not a literal of " << vhdl_type_to_string(type);
  }

  // Both typed; VHDL is strongly typed, so these must match.
  throw errort{}.with_location(source_location)
    << "type mismatch: expected " << vhdl_type_to_string(type) << ", got "
    << vhdl_type_to_string(source_type);
}

/// Convert a universal or overloaded literal to the type of the other
/// operand; when both are literals, pick a type.
void vhdl_typecheckt::match_literals(exprt &a, exprt &b)
{
  bool a_universal = is_vhdl_universal_type(a.type());
  bool b_universal = is_vhdl_universal_type(b.type());

  if(a_universal && b_universal)
  {
    a = literal_with_default_type(std::move(a));
    b = literal_with_default_type(std::move(b));
  }
  else if(a_universal)
    a = convert_to(std::move(a), vhdl_base_type(b.type()));
  else if(b_universal)
    b = convert_to(std::move(b), vhdl_base_type(a.type()));
}

/// IEEE 1076-2008 9.2: the operands of the predefined operators have
/// the same type, and arrays the same length. The operators of
/// numeric_std, std_logic_arith and std_logic_unsigned on a vector and
/// an integer are handled by the callers.
void vhdl_typecheckt::match_types(exprt &a, exprt &b)
{
  match_literals(a, b);

  if(vhdl_types_compatible(a.type(), b.type()))
  {
    if(
      a.type().id() == ID_vhdl_array && to_vhdl_array_type(a.type()).length() !=
                                          to_vhdl_array_type(b.type()).length())
      throw errort{}.with_location(a.source_location())
        << "the operands have different lengths: "
        << vhdl_type_to_string(a.type()) << " and "
        << vhdl_type_to_string(b.type());

    // the operands keep their subtypes; the result of an operator has
    // the base type (IEEE 1076-2008 9.2)
    return;
  }

  throw errort{}.with_location(a.source_location())
    << "the operands have different types: " << vhdl_type_to_string(a.type())
    << " and " << vhdl_type_to_string(b.type());
}

/// Whether the arithmetic and relational operators of numeric_std,
/// std_logic_arith, std_logic_unsigned or std_logic_signed apply to
/// the given vector type (IEEE 1076-2008 16.8), given the use clauses
bool vhdl_typecheckt::has_numeric_operators(const typet &type) const
{
  if(!is_vhdl_vector_type(type))
    return false;

  auto base = to_vhdl_array_type(type).base_name();

  if(base == "unsigned" || base == "signed")
    return uses_package("numeric_std") || uses_package("std_logic_arith");
  else if(base == "std_ulogic_vector")
    return uses_package("std_logic_unsigned") ||
           uses_package("std_logic_signed") ||
           uses_package("numeric_std_unsigned");
  else
    return false;
}

/// The numeric type that std_logic_unsigned, std_logic_signed and
/// numeric_std_unsigned give to a std_logic_vector: unsigned, or signed
/// with std_logic_signed.
typet vhdl_typecheckt::numeric_type_of(const typet &type) const
{
  PRECONDITION(has_numeric_operators(type));
  auto &array_type = to_vhdl_array_type(type);

  if(is_vhdl_numeric_vector_type(type))
    return type;

  bool is_signed =
    uses_package("std_logic_signed") && !uses_package("std_logic_unsigned");
  return vhdl_vector_type(
    is_signed ? "signed" : "unsigned", array_type.range());
}

/// IEEE 1076-2008 9.2.5: concatenation of arrays and elements.
/// The operands are two arrays of the same type, an array and an element
/// of its element type, or two elements of the same type.
exprt vhdl_typecheckt::typecheck_concatenation(
  exprt lhs,
  exprt rhs,
  const source_locationt &source_location)
{
  // the array type for two elements
  auto array_type_for_element =
    [](const typet &element_type) -> vhdl_array_typet
  {
    auto base = base_name_of(element_type);
    if(base == "bit")
      return vhdl_unconstrained_array_type("bit_vector");
    else if(base == "std_ulogic")
    {
      if(to_vhdl_enumeration_type(element_type).name() == "std_logic")
        return vhdl_unconstrained_array_type("std_logic_vector");
      else
        return vhdl_unconstrained_array_type("std_ulogic_vector");
    }
    else
      return vhdl_array_typet{irep_idt{}, element_type, vhdl_natural_type()};
  };

  // a literal operand takes its type from the other operand
  auto convert_literal = [&](exprt &literal, const exprt &other)
  {
    auto literal_id = literal.type().id();
    bool other_array = other.type().id() == ID_vhdl_array;

    if(literal_id == ID_char || literal_id == ID_vhdl_overloaded_literal)
    {
      // an element
      literal = convert_to(
        std::move(literal),
        other_array ? to_vhdl_array_type(other.type()).element_type()
                    : other.type());
    }
    else if(literal_id == ID_string || literal_id == ID_vhdl_bit_string)
    {
      // an array of the type of the other operand, with the length of
      // the literal
      auto unconstrained = other_array
                             ? to_vhdl_array_type(other.type()).unconstrained()
                             : array_type_for_element(other.type());
      literal = convert_to(std::move(literal), unconstrained);
    }
    else
      throw errort{}.with_location(literal.source_location())
        << "cannot concatenate this literal";
  };

  bool lhs_literal = is_vhdl_universal_type(lhs.type());
  bool rhs_literal = is_vhdl_universal_type(rhs.type());

  if(lhs_literal && rhs_literal)
  {
    lhs = literal_with_default_type(std::move(lhs));
    lhs_literal = false;
  }

  if(lhs_literal)
    convert_literal(lhs, rhs);
  else if(rhs_literal)
    convert_literal(rhs, lhs);

  bool lhs_array = lhs.type().id() == ID_vhdl_array;
  bool rhs_array = rhs.type().id() == ID_vhdl_array;

  auto element_type_of = [](const exprt &op) -> const typet &
  {
    return op.type().id() == ID_vhdl_array
             ? to_vhdl_array_type(op.type()).element_type()
             : op.type();
  };

  // the element types must match, e.g., bit_vector & std_logic is an error
  if(
    !vhdl_types_compatible(element_type_of(lhs), element_type_of(rhs)) ||
    (lhs_array && rhs_array && !vhdl_types_compatible(lhs.type(), rhs.type())))
    throw errort{}.with_location(source_location)
      << "cannot concatenate " << vhdl_type_to_string(lhs.type()) << " and "
      << vhdl_type_to_string(rhs.type());

  // the array type of the result
  vhdl_array_typet result_type = lhs_array ? to_vhdl_array_type(lhs.type())
                                 : rhs_array
                                   ? to_vhdl_array_type(rhs.type())
                                   : array_type_for_element(lhs.type());

  mp_integer lhs_length =
    lhs_array ? to_vhdl_array_type(lhs.type()).length() : 1;
  mp_integer rhs_length =
    rhs_array ? to_vhdl_array_type(rhs.type()).length() : 1;
  mp_integer length = lhs_length + rhs_length;

  // IEEE 1076-2008 9.2.5: if both operands are null arrays, the result
  // is the right operand. Otherwise, the direction of the result is
  // that of the index subtype S of the base type, and the left bound
  // is S'left, e.g., 0 to N-1 for bit_vector. (VHDL-87 took the left
  // bound and direction from the left operand.)
  vhdl_ranget range;
  if(lhs_array && rhs_array && length == 0)
    range = to_vhdl_array_type(rhs.type()).range();
  else
    range = result_type.range_for_length(length);

  result_type.set_range(range);

  return concatenation_exprt{std::move(lhs), std::move(rhs), result_type};
}

/// The arithmetic and relational operators of numeric_std,
/// std_logic_arith, std_logic_unsigned and std_logic_signed on two
/// vectors of the same type, or a vector and an integer
/// (IEEE 1076-2008 16.8.2). At least one operand is a numeric vector.
/// std_logic_vectors are converted to unsigned or signed; an integer
/// operand of an arithmetic operator is converted to the vector type,
/// as the packages do; comparisons with an integer are left to the
/// lowering, which compares at full precision.
exprt vhdl_typecheckt::typecheck_numeric_binary(
  irep_idt id,
  exprt lhs,
  exprt rhs,
  const source_locationt &source_location)
{
  // an integer literal is an integer; an array literal has the type of
  // the other operand
  auto convert_literal = [this](exprt &literal, const exprt &other)
  {
    if(literal.type().id() == ID_natural)
      literal = convert_to(std::move(literal), vhdl_integer_type());
    else if(is_vhdl_vector_type(other.type()))
      literal = convert_to(std::move(literal), other.type());
    else
      throw errort{}.with_location(literal.source_location())
        << "cannot determine the type of the literal";
  };

  if(is_vhdl_universal_type(lhs.type()))
    convert_literal(lhs, rhs);
  else if(is_vhdl_universal_type(rhs.type()))
    convert_literal(rhs, lhs);

  bool lhs_vector = is_vhdl_vector_type(lhs.type());
  bool rhs_vector = is_vhdl_vector_type(rhs.type());
  PRECONDITION(lhs_vector || rhs_vector);

  if(lhs_vector && rhs_vector)
  {
    if(!vhdl_types_compatible(lhs.type(), rhs.type()))
      throw errort{}.with_location(source_location)
        << "the operands have different types: "
        << vhdl_type_to_string(lhs.type()) << " and "
        << vhdl_type_to_string(rhs.type());
  }
  else
  {
    auto &other = lhs_vector ? rhs : lhs;
    if(!is_vhdl_integer_type(other.type()))
      throw errort{}.with_location(source_location)
        << "the operands have different types: "
        << vhdl_type_to_string(lhs.type()) << " and "
        << vhdl_type_to_string(rhs.type());
  }

  // the VHDL type of the vector operands; the std_logic_vector of
  // std_logic_unsigned is interpreted as unsigned
  const typet vector_type = lhs_vector ? lhs.type() : rhs.type();
  const typet numeric_type = numeric_type_of(vector_type);
  bool slv = numeric_type != vector_type;

  auto as_numeric = [&](exprt op) -> exprt
  {
    if(is_vhdl_vector_type(op.type()) && slv)
    {
      auto range = to_vhdl_array_type(op.type()).range();
      return typecast_exprt{
        std::move(op),
        vhdl_vector_type(to_vhdl_array_type(numeric_type).base_name(), range)};
    }
    else
      return op;
  };

  lhs = as_numeric(std::move(lhs));
  rhs = as_numeric(std::move(rhs));

  if(
    id == ID_equal || id == ID_notequal || id == ID_lt || id == ID_le ||
    id == ID_gt || id == ID_ge)
  {
    exprt result = binary_relation_exprt{std::move(lhs), id, std::move(rhs)};
    result.type() = vhdl_boolean_type();
    result.add_source_location() = source_location;
    return result;
  }

  // The integer operand is converted to the vector type. For + - and *
  // numeric_std converts it to L'length (16.8.4). For / rem and mod it
  // converts to MAX(L'length, the number of bits of the value), and
  // resizes the result to L'length; the integer operand is therefore
  // converted without loss, at the width of integer.
  auto integer_operand_type = [&](const typet &vector_type) -> typet
  {
    if(id == ID_div || id == ID_mod || id == ID_vhdl_rem)
    {
      auto &array_type = to_vhdl_array_type(vector_type);
      auto length = std::max(array_type.length(), mp_integer{32});
      return vhdl_vector_type(
        array_type.base_name(),
        vhdl_ranget{length - 1, 0, vhdl_directiont::DOWNTO});
    }
    else
      return vector_type;
  };

  if(!lhs_vector)
    lhs = typecast_exprt{std::move(lhs), integer_operand_type(rhs.type())};
  if(!rhs_vector)
    rhs = typecast_exprt{std::move(rhs), integer_operand_type(lhs.type())};

  auto lhs_length = to_vhdl_array_type(lhs.type()).length();
  auto rhs_length = to_vhdl_array_type(rhs.type()).length();

  // the length of the result of the arithmetic operators
  mp_integer result_length;

  if(id == ID_plus || id == ID_minus)
    result_length = std::max(lhs_length, rhs_length);
  else if(id == ID_mult)
    result_length = lhs_length + rhs_length;
  else if(id == ID_div)
    result_length = lhs_vector ? lhs_length : rhs_length;
  else if(id == ID_mod || id == ID_vhdl_rem)
  {
    // numeric_std 16.8.4, 16.8.5: R'length for two vectors
    result_length = lhs_vector && rhs_vector ? rhs_length
                    : lhs_vector             ? lhs_length
                                             : rhs_length;
  }
  else
    throw errort{}.with_location(source_location)
      << "operator " << id << " is not defined on "
      << vhdl_type_to_string(vector_type);

  vhdl_ranget range{result_length - 1, 0, vhdl_directiont::DOWNTO};
  auto result_type =
    vhdl_vector_type(to_vhdl_array_type(numeric_type).base_name(), range);

  exprt result = binary_exprt{std::move(lhs), id, std::move(rhs), result_type};
  result.add_source_location() = source_location;

  // back to std_logic_vector
  if(slv)
    return typecast_exprt{
      std::move(result),
      vhdl_constrained_array_type(to_vhdl_array_type(vector_type), range)};
  else
    return result;
}

exprt vhdl_typecheckt::typecheck_binary(exprt expr)
{
  auto &binary = to_binary_expr(expr);
  auto id = expr.id();
  auto &source_location = expr.source_location();

  auto lhs = typecheck_expr(binary.lhs());
  auto rhs = typecheck_expr(binary.rhs());

  if(id == ID_concatenation)
    return typecheck_concatenation(
      std::move(lhs), std::move(rhs), source_location);

  if(
    id == ID_shl || id == ID_lshr || id == ID_ashr || id == ID_vhdl_sla ||
    id == ID_rol || id == ID_ror)
  {
    // IEEE 1076-2008 9.2.4: the left operand is a one-dimensional array
    // of bit or boolean, the right operand an integer
    if(!is_vhdl_vector_type(lhs.type()))
      throw errort{}.with_location(source_location)
        << "shift requires a vector, got " << vhdl_type_to_string(lhs.type());

    // sla fills with the right-most element (9.2.8), which has no
    // CBMC counterpart
    if(id == ID_vhdl_sla)
      throw errort{}.with_location(source_location) << "sla is not supported";

    rhs = convert_to(std::move(rhs), vhdl_integer_type());
    auto type = lhs.type();
    return binary_exprt{std::move(lhs), id, std::move(rhs), type};
  }

  if(
    id == ID_and || id == ID_or || id == ID_nand || id == ID_nor ||
    id == ID_xor || id == ID_xnor)
  {
    // IEEE 1076-2008 9.2.2: both operands have the same type, which
    // is bit, boolean, or a one-dimensional array of these, and arrays
    // have the same length
    match_types(lhs, rhs);
    auto type = vhdl_base_type(lhs.type());

    if(
      !is_vhdl_scalar_bit_type(type) && base_name_of(type) != "boolean" &&
      !is_vhdl_vector_type(type))
      throw errort{}.with_location(source_location)
        << "logical operator requires boolean, bit or vector operands, got "
        << vhdl_type_to_string(type);

    exprt result = binary_exprt{std::move(lhs), id, std::move(rhs), type};
    result.add_source_location() = source_location;
    return result;
  }

  bool relational = id == ID_equal || id == ID_notequal || id == ID_lt ||
                    id == ID_le || id == ID_gt || id == ID_ge;
  bool arithmetic = id == ID_plus || id == ID_minus || id == ID_mult ||
                    id == ID_div || id == ID_mod || id == ID_vhdl_rem ||
                    id == ID_power;

  if(!relational && !arithmetic)
    throw errort{}.with_location(source_location)
      << "unexpected binary operator: " << id;

  // An array literal that is an operand of a relational or arithmetic
  // operator keeps its own length: the predefined relational operators
  // compare arrays of any lengths (IEEE 1076-2008 9.2.3), so v /= "10"
  // is legal for a longer v, and false; the arithmetic operators of
  // the numeric packages take vectors of different lengths, so
  // cnt + "1" is legal, with the length of cnt (numeric_std 16.8.4).
  {
    auto array_literal = [this](exprt &literal, const exprt &other)
    {
      auto id = literal.type().id();
      if(
        (id == ID_string || id == ID_vhdl_bit_string) &&
        other.type().id() == ID_vhdl_array)
        literal = convert_to(
          std::move(literal), to_vhdl_array_type(other.type()).unconstrained());
    };
    array_literal(lhs, rhs);
    array_literal(rhs, lhs);
  }

  // the operators on time
  if(
    lhs.type().id() == ID_vhdl_physical_type ||
    rhs.type().id() == ID_vhdl_physical_type)
    return typecheck_physical_binary(
      id, std::move(lhs), std::move(rhs), source_location);

  // the operators of the numeric packages on vectors
  if(
    id != ID_power &&
    (has_numeric_operators(lhs.type()) || has_numeric_operators(rhs.type())))
    return typecheck_numeric_binary(
      id, std::move(lhs), std::move(rhs), source_location);

  if(
    arithmetic &&
    (is_vhdl_vector_type(lhs.type()) || is_vhdl_vector_type(rhs.type())))
  {
    auto &vector_type =
      is_vhdl_vector_type(lhs.type()) ? lhs.type() : rhs.type();
    throw errort{}.with_location(source_location)
      << "arithmetic on " << vhdl_type_to_string(vector_type)
      << " requires the package numeric_std, std_logic_arith or "
         "std_logic_unsigned";
  }

  // two literals, e.g., "1" < "10"
  if(is_vhdl_universal_type(lhs.type()) && is_vhdl_universal_type(rhs.type()))
  {
    lhs = literal_with_default_type(std::move(lhs));
    rhs = literal_with_default_type(std::move(rhs));
  }

  if(
    relational && lhs.type().id() == ID_vhdl_array &&
    rhs.type().id() == ID_vhdl_array)
  {
    // IEEE 1076-2008 9.2.3: the predefined operators on arrays; the
    // arrays may have different lengths
    if(!vhdl_types_compatible(lhs.type(), rhs.type()))
      throw errort{}.with_location(source_location)
        << "the operands have different types: "
        << vhdl_type_to_string(lhs.type()) << " and "
        << vhdl_type_to_string(rhs.type());

    if(
      (id != ID_equal && id != ID_notequal) && !is_vhdl_vector_type(lhs.type()))
      throw errort{}.with_location(source_location)
        << "relational operators on arrays are only supported for vectors";

    exprt result = binary_relation_exprt{std::move(lhs), id, std::move(rhs)};
    result.type() = vhdl_boolean_type();
    result.add_source_location() = source_location;
    return result;
  }

  // both operands have the same type
  match_types(lhs, rhs);
  auto type = vhdl_base_type(lhs.type());

  if(id == ID_equal || id == ID_notequal)
  {
    exprt result = binary_relation_exprt{std::move(lhs), id, std::move(rhs)};
    result.type() = vhdl_boolean_type();
    result.add_source_location() = source_location;
    return result;
  }
  else if(relational)
  {
    // the ordering relations on the scalar types
    if(type.id() != ID_vhdl_enumeration && type.id() != ID_vhdl_integer)
      throw errort{}.with_location(source_location)
        << "relational operator requires scalar or vector operands, got "
        << vhdl_type_to_string(type);

    exprt result = binary_relation_exprt{std::move(lhs), id, std::move(rhs)};
    result.type() = vhdl_boolean_type();
    result.add_source_location() = source_location;
    return result;
  }
  else // arithmetic
  {
    if(!is_vhdl_integer_type(type))
      throw errort{}.with_location(source_location)
        << "arithmetic operator requires integer operands, got "
        << vhdl_type_to_string(type);

    if(id == ID_power)
    {
      // IEEE 1076-2008 9.2.8: the exponent is an integer; we require
      // a static expression
      auto base = constant_value(lhs);
      auto exponent = constant_value(rhs);

      if(!base.has_value() || !exponent.has_value())
        throw errort{}.with_location(source_location)
          << "** requires static operands";

      if(*exponent < 0)
        throw errort{}.with_location(source_location)
          << "the exponent of ** must not be negative";

      // the result must be an integer; avoid computing huge powers
      if(*exponent > 40 && *base != 0 && *base != 1 && *base != -1)
        throw errort{}.with_location(source_location)
          << "the value of " << *base << "**" << *exponent
          << " is outside of the range of integer";

      auto value = power(*base, *exponent);

      if(value < -power(2, 31) || value >= power(2, 31))
        throw errort{}.with_location(source_location)
          << "the value " << value << " is outside of the range of integer";

      auto result = vhdl_integer_constant(value, type);
      result.add_source_location() = source_location;
      return std::move(result);
    }

    exprt result = binary_exprt{std::move(lhs), id, std::move(rhs), type};
    result.add_source_location() = source_location;
    return result;
  }
}

exprt vhdl_typecheckt::typecheck_unary(exprt expr)
{
  auto id = expr.id();
  auto op = typecheck_expr(to_unary_expr(expr).op());

  if(id == ID_typecast)
  {
    // the VHDL-2008 condition operator ??
    if(is_vhdl_universal_type(op.type()))
      op = convert_to(std::move(op), vhdl_std_logic_type());
    if(
      !is_vhdl_scalar_bit_type(op.type()) &&
      base_name_of(op.type()) != "boolean")
      throw errort{}.with_location(expr.source_location())
        << "?? requires a bit or boolean";
    return typecast_exprt{std::move(op), vhdl_boolean_type()};
  }

  if(id == ID_unary_minus && op.type().id() == ID_natural)
  {
    // The negation of an integer literal, e.g., -2147483648, which is
    // in the range of integer even when the literal is not
    auto value = -integer_literal_value(to_constant_expr(op));

    if(value < -power(2, 31) || value >= power(2, 31))
      throw errort{}.with_location(expr.source_location())
        << "the value " << value << " is outside of the range of integer";

    auto result = vhdl_integer_constant(value, vhdl_integer_type());
    result.add_source_location() = expr.source_location();
    return std::move(result);
  }

  if(is_vhdl_universal_type(op.type()))
    op = literal_with_default_type(std::move(op));

  auto type = op.type();

  if(id == ID_not)
  {
    if(
      !is_vhdl_scalar_bit_type(type) && base_name_of(type) != "boolean" &&
      !is_vhdl_vector_type(type))
      throw errort{}.with_location(expr.source_location())
        << "not requires a boolean, bit or vector operand, got "
        << vhdl_type_to_string(type);

    return unary_exprt{ID_not, std::move(op), type};
  }
  else if(id == ID_unary_minus || id == ID_unary_plus || id == ID_abs)
  {
    // IEEE 1076-2008 9.2.6, numeric_std: integers, and signed
    bool numeric_signed = has_numeric_operators(type) &&
                          base_name_of(numeric_type_of(type)) == "signed";

    if(!is_vhdl_integer_type(type) && !numeric_signed)
      throw errort{}.with_location(expr.source_location())
        << "arithmetic operator requires an integer or signed operand, got "
        << vhdl_type_to_string(type);

    if(id == ID_unary_plus)
      return op;

    if(numeric_signed && !is_vhdl_numeric_vector_type(type))
    {
      // std_logic_signed: through signed
      auto numeric = numeric_type_of(type);
      exprt result =
        unary_exprt{id, typecast_exprt{std::move(op), numeric}, numeric};
      return typecast_exprt{std::move(result), type};
    }

    return unary_exprt{id, std::move(op), type};
  }
  else
    throw errort{}.with_location(expr.source_location())
      << "unexpected unary operator: " << id;
}
